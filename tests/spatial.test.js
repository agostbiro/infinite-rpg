import { test } from 'node:test';
import assert from 'node:assert/strict';
import { portalsForView, inputKey, figuresForView, interactionPoints, nearestPoint, pointRadius, namesCharacter } from '../web/spatial.js';
import { arrivalForLayout } from '../web/travel.js';

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

// Walk straight from the arrival toward a point, with people and objects solid, until its menu
// shows. On the way, the menu of a closer neighbour can show for a moment.
function walkUntilMenu(layout, target) {
  const solid = layout.points.map(p => ({ x: p.x, z: p.z, radius: pointRadius(p) }));
  let position = arrivalForLayout(layout);
  for (let step = 0; step < 400; step++) {
    const menu = nearestPoint(position, layout.points);
    if (menu?.id === target.id) return menu;
    const dx = target.x - position.x, dz = target.z - position.z, d = Math.hypot(dx, dz);
    position = moveInWorld(position, dx / d * 0.05, dz / d * 0.05, solid, layout.bound);
  }
  return null;
}

const mixedLabels = ['Open the door', 'Climb the ladder', 'Talk to the guard', 'Read the map', 'Run for the ferry', 'Follow the river road'];

test('the menu of each point shows when the Player walks up to it from the arrival', () => {
  for (let count = 1; count <= mixedLabels.length; count++) {
    const view = viewFor(count);
    view.scene.choices.forEach((c, i) => { c.text = mixedLabels[i]; });
    const layout = worldLayout(interactionPoints(view, portalsForView(view)), place);
    assert.equal(nearestPoint(arrivalForLayout(layout), layout.points), null, 'no menu at the arrival');
    for (const target of layout.points.filter(p => p.actions.length)) {
      assert.equal(walkUntilMenu(layout, target)?.id, target.id, count + ' points: ' + target.id);
    }
  }
});

test('movement and waiting do not mutate logical state or invent an exit', () => {
  const view = viewFor(3);
  const before = JSON.stringify(view);
  const layout = worldLayout(interactionPoints(view, portalsForView(view)), place);
  let p = arrivalForLayout(layout);
  for (let i = 0; i < 1000; i++) p = moveInWorld(p, Math.cos(i) * 0.1, Math.sin(i) * 0.1, [], layout.bound);
  assert.equal(JSON.stringify(view), before);
  const atWall = moveInWorld(p, 10000, 10000, [], layout.bound);
  assert.deepEqual(atWall, { x: layout.bound, z: layout.bound });
});

/** The points of a Scene with these Choice texts and this cast. */
function pointsFor(texts, npcs) {
  const view = viewFor(texts.length);
  view.scene.id = 1;
  view.scene.choices.forEach((c, i) => { c.text = texts[i]; });
  if (npcs) view.environment = { scenes: [{ scene: 1, place: 0, npcs }] };
  const portals = portalsForView(view);
  return { view, portals, points: interactionPoints(view, portals) };
}

/** Every offered input is in exactly one point. */
function assertEachInputOnce(portals, points) {
  const keys = points.flatMap(p => p.actions.map(a => a.key));
  assert.deepEqual([...keys].sort(), portals.map(p => p.key).sort());
}

test('one figure per character holds all the Choices that talk to it or name it', () => {
  // The Militia Camp of the built-in Adventure: two ways to ask Captain Hollis, and one to leave.
  const { portals, points } = pointsFor([
    'Ask him, as one soldier to another (Diplomacy -1)',
    'Tell him that General Washington asks it of him (Fast-Talk)',
    'Leave them and march on'], ['Captain Hollis']);
  assertEachInputOnce(portals, points);
  assert.deepEqual(points.map(p => [p.kind, p.title, p.actions.length]),
    [['figure', 'Captain Hollis', 2], ['marker', 'What next?', 1]]);
  // A Choice that names a character goes to that character, whatever its look.
  const named = pointsFor(['Go ahead with Jem to scout the ford (Survival)', 'Ask the Oneida warriors to cover the crossing'],
    ['Jem', 'Oneida Warrior']);
  assertEachInputOnce(named.portals, named.points);
  assert.deepEqual(named.points.map(p => [p.title, p.actions.map(a => a.label)]), [
    ['Jem', ['Go ahead with Jem to scout the ford (Survival)']],
    ['Oneida Warrior', ['Ask the Oneida warriors to cover the crossing']]]);
});

test('Choices with no known object share one marker, and talk with no cast gets one Traveller', () => {
  const { portals, points } = pointsFor(['Rush the scout', 'Creep up behind him (Stealth -1)', 'Talk him down', 'Ask for a sign', 'Open the chest']);
  assertEachInputOnce(portals, points);
  assert.deepEqual(points.map(p => [p.kind, p.actions.length]), [['marker', 2], ['figure', 2], ['object', 1]]);
  assert.equal(new Set(points.map(p => p.id)).size, points.length);
});

test('a Fight draws each foe once, in front of the way the Player looks', () => {
  const attack = target => ({ maneuver: { m: 'attack', target } });
  const view = {
    phase: 'fight', inputs: [attack(0), attack(1)],
    fight: { foes: [{ name: 'Grenadier 1', hp: 11, alive: true }, { name: 'Grenadier 2', hp: 11, alive: true }],
      maneuvers: [{ label: 'Attack', attacks: true, options: [0, 1].map(target => ({ target, input: attack(target) })) }] },
  };
  const points = interactionPoints(view, portalsForView(view));
  assert.deepEqual(points.map(p => [p.kind, p.title, p.actions.length]), [['figure', 'Grenadier 1', 0], ['figure', 'Grenadier 2', 0]]);
  for (const yaw of [0, 0.8, -2.5, Math.PI]) {
    const anchor = { x: 10, z: -4 };
    const layout = worldLayout(points, place, anchor, null, yaw);
    const forward = { x: -Math.sin(yaw), z: -Math.cos(yaw) };
    for (const foe of layout.points) {
      const dx = foe.x - anchor.x, dz = foe.z - anchor.z, d = Math.hypot(dx, dz);
      // Each foe is ahead, within 20 degrees of the centre of the view.
      assert.ok((dx * forward.x + dz * forward.z) / d > Math.cos(20 * Math.PI / 180), 'yaw ' + yaw);
    }
  }
});

test('a character name matches in any case, with a plural, but not inside another word', () => {
  assert.ok(namesCharacter('Ask the Oneida warriors', 'Oneida Warrior'));
  assert.ok(namesCharacter('jem knows the way', 'Jem'));
  assert.ok(!namesCharacter('Ride to the ridge', 'Jem'));
  assert.ok(!namesCharacter('Talk to Bjem', 'Jem'));
});

test('input identity does not depend on JSON field order', () => {
  assert.equal(inputKey({ maneuver: { m: 'attack', target: 0 } }), inputKey({ maneuver: { target: 0, m: 'attack' } }));
});

test('narrative objects come from the Choice text without changing the offered commands', () => {
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
