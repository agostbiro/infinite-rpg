import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { arrivalForLayout, planTransition, transitionAt, shortestTurn, GLIDE_LIMIT, DEFAULT_PITCH } from '../web/travel.js';
import { environmentFor, placeForScene, eventAnchorForScene, worldLayout, sceneryFor, propRadius } from '../web/environment.js';
import { portalsForView, interactionPoints, nearestPoint } from '../web/spatial.js';
import { SpatialGame } from '../web/world3d.js';

// A small story and its world map, only for these tests.
const campaign = JSON.parse(fs.readFileSync(new URL('./spatial-world.json', import.meta.url)));
const viewForScene = scene => {
  const inputs = scene.choices.map((_, choice) => ({ choose: { choice } }));
  return { phase: 'scene', inputs, scene: { ...scene, choices: scene.choices.map((c, i) => ({ ...c, input: inputs[i] })) } };
};
const layoutFor = (environment, scene) => {
  const view = viewForScene(scene);
  return worldLayout(interactionPoints(view, portalsForView(view)), placeForScene(environment, scene.id), null, eventAnchorForScene(environment, scene.id));
};
const distance = (a, b) => Math.hypot(a.x-b.x, a.z-b.z);
const angleGap = (a, b) => Math.abs(shortestTurn(a, b));

test('every Scene of the test story has a clear arrival, out of reach of every menu', () => {
  const before = JSON.stringify(campaign), env = campaign.environment;
  const obstacles = sceneryFor(env).filter(p => p.kind !== 'river').map(p => ({ ...p, radius: propRadius(p) }));
  for (const scene of campaign.scenes) {
    const layout = layoutFor(env, scene), arrival = arrivalForLayout(layout);
    for (const obstacle of obstacles) assert.ok(distance(arrival, obstacle) >= obstacle.radius + 0.4, `scene ${scene.id}`);
    assert.equal(nearestPoint(arrival, layout.points), null, `scene ${scene.id}`);
  }
  assert.equal(JSON.stringify(campaign), before);
});

test('a short move glides and a long move fades, and both take under one second', () => {
  const near = planTransition({ x: 0, z: 0 }, { x: GLIDE_LIMIT - 1, z: 0 }, 0, 0);
  const far = planTransition({ x: 0, z: 0 }, { x: 80, z: -60 }, 0, 0);
  const turnAround = planTransition({ x: 0, z: 0 }, { x: 2, z: 0 }, Math.PI, 0);
  assert.equal(near.kind, 'glide');
  assert.equal(far.kind, 'fade');
  assert.equal(turnAround.kind, 'fade', 'a big turn fades, so the Player does not see a fast spin');
  for (const plan of [near, far, turnAround]) assert.ok(plan.duration > 0 && plan.duration < 1);
});

test('a transition ends at the arrival, facing the points, and never jumps', () => {
  const from = { x: -70, z: 64 }, to = { x: -25, z: 75 };
  for (const [startYaw, target] of [[0.76, 0], [-3, 2.9], [Math.PI, 0], [0, 0]]) {
    for (const plan of [planTransition(from, to, startYaw, 0.4, target), planTransition(from, { x: -66, z: 62 }, startYaw, 0.4, target)]) {
      const end = transitionAt(plan, plan.duration);
      assert.ok(end.done);
      assert.ok(distance(end.position, plan.to) < 1e-9);
      assert.ok(angleGap(end.yaw, target) < 1e-9);
      assert.ok(Math.abs(end.pitch - DEFAULT_PITCH) < 1e-12);
      assert.equal(end.fade, 0);
      // The camera at the start is the camera before the transition.
      const start = transitionAt(plan, 0);
      assert.equal(start.yaw, startYaw);
      assert.deepEqual(start.position, from);
      // At 60 frames a second, a glide moves and turns a little in each frame. A fade moves and
      // turns the camera only while the screen is black.
      let previous = start;
      for (let t = 1 / 60; t <= plan.duration + 1 / 60; t += 1 / 60) {
        const now = transitionAt(plan, t);
        const turned = angleGap(now.yaw, previous.yaw), moved = distance(now.position, previous.position);
        if (plan.kind === 'glide') assert.ok(turned < 0.1 && moved < 0.5, `glide at ${t}`);
        else if (turned > 0 || moved > 0) assert.equal(Math.min(now.fade, previous.fade), 1, `fade at ${t}`);
        previous = now;
      }
    }
  }
});

test('the shortest turn goes the short way round', () => {
  assert.ok(Math.abs(shortestTurn(3, -3) - (2 * Math.PI - 6)) < 1e-12);
  assert.ok(Math.abs(shortestTurn(0.5, 0) + 0.5) < 1e-12);
});

test('authored mappings fail closed if a graph update leaves a scene unmapped', () => {
  const env = structuredClone(campaign.environment);
  env.scenes = env.scenes.filter(s => s.scene !== 0);
  assert.throws(() => placeForScene(env, 0), /no valid place/);
  const fallback = environmentFor({adventure:'Older adventure'});
  assert.ok(placeForScene(fallback, 999));
});

function rendererHarness(t) {
  const previousDocument = globalThis.document;
  const previousStorage = Object.getOwnPropertyDescriptor(globalThis, 'localStorage');
  Object.defineProperty(globalThis, 'localStorage', {configurable:true, value:{getItem() { return null; }}});
  const elements = new Map();
  globalThis.document = {
    getElementById(id) {
      if (!elements.has(id)) elements.set(id, { hidden: true, dataset: {}, textContent: '', style: {} });
      return elements.get(id);
    },
    body: { classList: { toggle() {}, contains() { return false; } } },
    querySelector() { return null; },
  };
  t.after(() => {
    globalThis.document = previousDocument;
    if (previousStorage) Object.defineProperty(globalThis, 'localStorage', previousStorage);
    else delete globalThis.localStorage;
  });
  const sent = [], builds = [];
  const game = Object.create(SpatialGame.prototype);
  Object.assign(game, {
    root: {dataset:{}}, keys:new Set(), touches:new Map(), actors:[], travel:null, travelSceneKey:'',
    pending:false, paused:false, active:true, reducedMotion:{matches:false},
    buildWorld() { this.obstacles = []; },
    buildRoom(view) { builds.push(structuredClone(view)); },
    combatActions() {}, resize() {}, savePosition() {}, pause() {},
    onChoose: async input => { sent.push(input); },
  });
  const view = {
    phase:'scene', seed:7, adventure:'Test adventure', world:'Test world',
    environment:structuredClone(campaign.environment), scene:structuredClone(campaign.scenes[0]),
    inputs:[{choose:{choice:0}},{choose:{choice:1}}], reports:[], character:{name:'Hero',hp:11,maxHP:11},
  };
  view.scene.choices = view.scene.choices.map((c,i) => ({...c,input:view.inputs[i]}));
  return {game, view, sent, builds, elements};
}

/** The view after the Player picks a Choice that leads to Scene `id` of the test story. With
 * `roll`, the Choice rolls a skill first. */
function nextScene(view, id, roll = false) {
  const next = structuredClone(view);
  next.scene = structuredClone(campaign.scenes.find(s => s.id === id));
  next.inputs = next.scene.choices.map((_, choice) => ({ choose: { choice } }));
  next.scene.choices = next.scene.choices.map((c, i) => ({ ...c, input: next.inputs[i] }));
  const rolled = roll ? [{ successRoll: { who: 'Hero', what: 'Diplomacy', roll: { target: 12, total: 9, faces: [3, 3, 3], result: 'success' } } }] : [];
  next.reports = [...view.reports, { picked: { text: 'Go' } }, ...rolled, { scene: { id } }];
  return next;
}

test('the first Scene starts at its arrival with no transition', t => {
  const {game, view} = rendererHarness(t);
  game.update(view, false);
  game.update(view, true);
  assert.equal(game.travel, null);
  assert.ok(distance(game.position, arrivalForLayout(game.layout)) < 1e-9);
  assert.equal(game.yaw, 0);
});

test('the renderer waits for playback, ignores polling, and blocks moves and Choices during a transition', async t => {
  const {game, view, sent, elements} = rendererHarness(t);
  game.update(view, true);
  game.yaw = 1.2;
  const next = nextScene(view, 1, true);
  game.update(next, false);
  assert.equal(game.travel, null, 'no transition while Reports play');
  game.update(next, true);
  // The result of the Choice stays on screen until the Player presses Continue.
  assert.equal(game.travel, null, 'no transition before Continue');
  assert.equal(game.waiting, true);
  assert.equal(elements.get('world-continue').hidden, false);
  assert.equal(game.canMove(), false);
  game.update(structuredClone(next), true);
  assert.equal(game.travel, null, 'a poll does not start the transition');
  game.continueOn();
  assert.equal(elements.get('world-continue').hidden, true);
  const trip = game.travel;
  assert.ok(trip);
  game.update(structuredClone(next), true);
  assert.equal(game.travel, trip, 'a poll does not restart the transition');
  // No move and no Choice while it plays.
  assert.equal(game.canMove(), false);
  const before = { ...game.position };
  game.move(5, 5);
  assert.deepEqual(game.position, before);
  await game.choose(game.layout.points.find(p => p.actions.length).actions[0]);
  assert.deepEqual(sent, []);
  // The next Scene is far away, so the screen fades. The camera turns and moves only while it is black.
  assert.equal(trip.plan.kind, 'fade');
  game.travelFrame(trip.plan.duration * 0.25);
  assert.equal(game.yaw, 1.2);
  assert.ok(Number(elements.get('world-travel').style.opacity) > 0);
  game.travelFrame(trip.plan.duration * 0.3);
  assert.equal(elements.get('world-travel').style.opacity, '1');
  assert.ok(distance(game.position, arrivalForLayout(game.layout)) < 1e-9);
  game.travelFrame(trip.plan.duration);
  assert.equal(game.travel, null);
  assert.ok(distance(game.position, arrivalForLayout(game.layout)) < 1e-9);
  assert.ok(angleGap(game.yaw, 0) < 1e-9);
  assert.deepEqual(sent, []);
  game.update(next, true);
  assert.equal(game.travel, null);
  assert.equal(game.canMove(), true);
  await game.choose(game.layout.points.find(p => p.actions.length).actions[0]);
  assert.equal(sent.length, 1);
});

test('the renderer refreshes changed options, NPCs and scene placement', t => {
  const {game, view, builds} = rendererHarness(t);
  game.update(view, true);
  const changed = structuredClone(view);
  changed.scene.choices[0].text = 'Read the new map';
  game.update(changed, true);
  assert.equal(builds.length, 2);
  assert.ok(game.layout.points.some(p => p.actions.some(a => a.label === 'Read the new map')));
  assert.equal(game.travel, null);
  const next = nextScene(changed, 1);
  next.environment.scenes.find(s => s.scene === next.scene.id).npcs = ['New guide'];
  game.update(next, true);
  assert.equal(game.layout.place.id, next.environment.scenes.find(s => s.scene === 1).place);
  // A plain Choice with no roll starts the trip at once, with no Continue.
  assert.ok(game.travel);
  assert.ok(!game.waiting);
  assert.equal(builds.length, 3);
  assert.ok(game.layout.points.some(p => p.kind === 'figure' && p.title === 'New guide'));
  game.travelFrame(1);
  game.update(next, true);
  assert.equal(game.travel, null);
});
