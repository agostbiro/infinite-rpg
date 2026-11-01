import { test } from 'node:test';
import assert from 'node:assert/strict';
import { portalsForView, crossedPortal, inputKey, figuresForView } from '../web/spatial.js';

import {worldLayout,moveInWorld} from '../web/environment.js';
const place={id:0,x:0,z:0};
const choose = choice => ({ choose: { choice } });
const viewFor = count => ({
  phase: 'scene', inputs: Array.from({ length: count }, (_, i) => choose(i)),
  scene: { choices: Array.from({ length: count }, (_, i) => ({ text: 'Choice ' + i, input: choose(i) })) },
});

test('portals carry exactly the server inputs, including repeated labels and destinations', () => {
  const view = viewFor(3);
  view.scene.choices.forEach(c => { c.text = 'The same label'; });
  const before = JSON.stringify(view);
  const ports = portalsForView(view);
  assert.deepEqual(ports.map(p => p.input), view.inputs);
  assert.equal(JSON.stringify(view), before);
  assert.equal(new Set(ports.map(p => p.key)).size, 3);
});

test('unoffered and disabled choices never become portals', () => {
  const view = viewFor(2);
  view.scene.choices.push({ text: 'Forbidden shortcut', input: choose(999) });
  view.scene.choices.push({ text: 'Disabled', input: null });
  assert.equal(portalsForView(view).length, 2);
});

test('missing and duplicate mappings fail closed instead of silently losing a choice', () => {
  const missing = viewFor(2);
  missing.scene.choices.pop();
  assert.throws(() => portalsForView(missing), /every offered input/);
  const duplicate = viewFor(1);
  duplicate.scene.choices.push(duplicate.scene.choices[0]);
  assert.throws(() => portalsForView(duplicate), /twice/);
});

test('combat represents every allowed maneuver and target, including defense', () => {
  const attack = target => ({ maneuver: { m: 'attack', target } });
  const defense = { maneuver: { m: 'allOutDefense', target: null } };
  const view = {
    phase: 'fight', inputs: [attack(0), attack(1), defense],
    fight: {
      foes: [{ name: 'Goblin' }, { name: 'Wolf' }],
      maneuvers: [
        { label: 'Attack', attacks: true, options: [0, 1].map(target => ({ target, input: attack(target) })) },
        { label: 'Defense', attacks: false, options: [{ target: null, input: defense }] },
      ],
    },
  };
  assert.deepEqual(portalsForView(view).map(p => p.input), view.inputs);
  assert.match(portalsForView(view)[1].label, /Wolf/);
});

test('terminal states expose no logical exit', () => {
  for (const phase of ['ended', 'dead', 'title']) assert.deepEqual(portalsForView({ ...viewFor(2), phase }), []);
});

test('each supported scene choice is reachable directly without crossing another choice', () => {
  for (let count = 1; count <= 4; count++) {
    const layout = worldLayout(portalsForView(viewFor(count)),place);
    for (const target of layout.portals) {
      let position = layout.spawn;
      let crossed = null;
      // Simulate the same movement and crossing functions used in the actual renderer.
      for (let step = 1; step <= 150; step++) {
        const fraction = step / 150;
        const intended = {
          x: layout.spawn.x + fraction * (target.x - layout.spawn.x),
          z: layout.spawn.z + fraction * (target.z - layout.spawn.z),
        };
        const next = moveInWorld(position, intended.x - position.x, intended.z - position.z, [], layout.bound);
        crossed = crossedPortal(position, next, layout.portals);
        position = next;
        if (crossed) break;
      }
      assert.equal(crossed?.key, target.key, 'gate ' + target.index + ' of ' + count);
    }
  }
});

test('movement and waiting do not mutate logical state or invent an exit', () => {
  const view = viewFor(3);
  const before = JSON.stringify(view);
  const layout = worldLayout(portalsForView(view),place);
  let p = layout.spawn;
  for (let i = 0; i < 1000; i++) {
    const next = moveInWorld(p, Math.cos(i) * 0.1, Math.sin(i) * 0.1, [], layout.bound);
    assert.equal(crossedPortal(p, next, layout.portals), null);
    p = next;
  }
  assert.equal(JSON.stringify(view), before);
  const atWall = moveInWorld(p, 10000, 10000, [], layout.bound);
  assert.deepEqual(atWall,{x:layout.bound,z:layout.bound});
});

test('swept gate detection does not miss a crossing between frames or resend inside a gate', () => {
  const gate = { key: 'a', x: 0, z: 0 };
  assert.equal(crossedPortal({ x: 0, z: 2 }, { x: 0, z: -2 }, [gate]), gate);
  assert.equal(crossedPortal({ x: 0, z: 0 }, { x: 0, z: 0.1 }, [gate]), null);
  assert.equal(crossedPortal({ x: 2, z: 2 }, { x: 2, z: -2 }, [gate]), null);
});

test('input identity does not depend on JSON field order', () => {
  assert.equal(inputKey({ maneuver: { m: 'attack', target: 0 } }), inputKey({ maneuver: { target: 0, m: 'attack' } }));
});

test('narrative objects replace generic gates without changing the offered commands', () => {
  const examples = [
    ['Climb the goat path', 'ladder'], ['Run for the ferry', 'boat'],
    ['Talk him down', 'person'], ['Swim across', 'water'], ['Pick the lock quietly', 'door'],
    ['Slip through the window', 'window'], ['Read the clouds', 'lookout'],
    ['Open the chest', 'chest'], ['Follow the stranger', 'path'], ['Stand and fight', 'sword'],
  ];
  const view = viewFor(examples.length);
  view.scene.choices.forEach((c, i) => { c.text = examples[i][0]; });
  const objects = portalsForView(view);
  assert.deepEqual(objects.map(p => p.visual.type), examples.map(e => e[1]));
  assert.deepEqual(objects.map(p => p.input), view.inputs);
});

test('NPC decoration introduces no commands, while combat figures retain the engine health', () => {
  const view = viewFor(1);
  view.scene.text = "Old Mother Burrows hammers on your gate. A grey wolf waits.";
  const before = JSON.stringify(view);
  assert.deepEqual(figuresForView(view).map(f => f.name), ['Old Mother Burrows', 'Grey wolf']);
  assert.equal(JSON.stringify(view), before);
  const fight = { fight: { foes: [{ name: 'Grey Wolf', hp: 3, maxHP: 9, alive: true }, { name: 'Guard', hp: 0, maxHP: 10, alive: false }] } };
  assert.deepEqual(figuresForView(fight).map(f => [f.name, f.hp, f.alive]), [['Grey Wolf', 3, true], ['Guard', 0, false]]);
});
