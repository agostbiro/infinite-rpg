import { test } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { planTravel, advanceTravel, arrivalForLayout } from '../web/travel.js';
import { environmentFor, placeForScene, eventAnchorForScene, worldLayout, sceneryFor, propRadius } from '../web/environment.js';
import { portalsForView } from '../web/spatial.js';
import { SpatialGame } from '../web/world3d.js';

const campaign = JSON.parse(fs.readFileSync(new URL('../campaigns/napoleon.json', import.meta.url)));
const layoutFor = (environment, scene) => {
  const view = { phase: 'scene', inputs: scene.choices.map((_, choice) => ({ choose: { choice } })),
    scene: { ...scene, choices: scene.choices.map((c, choice) => ({ ...c, input: { choose: { choice } } })) } };
  return worldLayout(portalsForView(view), placeForScene(environment, scene.id), null, eventAnchorForScene(environment, scene.id));
};
const distance = (a, b) => Math.hypot(a.x-b.x, a.z-b.z);

// Exercise the actual route planner, collisions and movement on every authored event edge.
test('every Napoleon outcome reaches a safe arrival without changing graph data', () => {
  const before = JSON.stringify(campaign), env = campaign.environment;
  const obstacles = sceneryFor(env).filter(p => p.kind !== 'river').map(p => ({ ...p, radius: propRadius(p) }));
  for (const scene of campaign.scenes) {
    const fromLayout = layoutFor(env, scene);
    for (const [i, choice] of scene.choices.entries()) {
      const o = choice.outcome;
      const targets = o.type === 'roll' ? [o.onSuccess, o.onFailure] : [o.type === 'fight' ? o.onWin : o.next];
      for (const id of targets) {
        const layout = layoutFor(env, campaign.scenes.find(s => s.id === id));
        let position = fromLayout.portals[i], index = 0, done = false;
        const route = planTravel(env, position, layout, obstacles);
        assert.ok(route, `${scene.id} -> ${id}`);
        for (let frame = 0; frame < 1000 && !done; frame++) {
          const step = advanceTravel(position, route, index, 0.8, obstacles, layout.bound);
          assert.equal(step.blocked, false, `${scene.id} -> ${id}`);
          ({ position, index, done } = step);
          for (const obstacle of obstacles) assert.ok(distance(position, obstacle) >= obstacle.radius+0.4-1e-8);
        }
        assert.ok(done);
        assert.ok(distance(position, arrivalForLayout(layout)) < 1e-7);
        for (const option of layout.portals) assert.ok(distance(position, option) > 2.1);
      }
    }
  }
  assert.equal(JSON.stringify(campaign), before);
});

test('travel follows declared paths and recomputes when those paths change', () => {
  const env = { places: [{id:0,x:0,z:0},{id:1,x:40,z:0},{id:2,x:40,z:40},{id:3,x:0,z:40}],
    paths: [{fromPlace:0,toPlace:1},{fromPlace:1,toPlace:2},{fromPlace:2,toPlace:3}] };
  const layout = worldLayout([], env.places[3]);
  const route = planTravel(env, env.places[0], layout, []);
  assert.ok(route.length >= 120);
  assert.ok(route.waypoints.some(p => p.x === 40 && p.z === 0));
  env.paths.push({fromPlace:0,toPlace:3});
  assert.ok(planTravel(env, env.places[0], layout, []).length < route.length);
  env.paths = [{fromPlace:0,toPlace:1}];
  assert.equal(planTravel(env, env.places[0], layout, []), null);
});

test('collisions stop a stale route, while a large frame still lands exactly at arrival', () => {
  const env = {places:[{id:0,x:0,z:0},{id:1,x:40,z:0}],paths:[{fromPlace:0,toPlace:1}]};
  const layout = worldLayout([], env.places[1]);
  const route = planTravel(env, env.places[0], layout, []);
  const blocked = advanceTravel(env.places[0], route, 0, 200, [{x:20,z:0,radius:3}], 115);
  assert.ok(blocked.blocked);
  assert.equal(blocked.done, false);
  const arrived = advanceTravel(env.places[0], route, 0, 200, [], 115);
  assert.ok(arrived.done);
  assert.deepEqual(arrived.position, route.arrival);
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
      if (!elements.has(id)) elements.set(id, { hidden: true, dataset: {}, textContent: '' });
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
  return {game, view, sent, builds};
}

test('the real renderer waits for playback, ignores polling, and cannot choose during travel', async t => {
  const {game, view, sent} = rendererHarness(t);
  game.update(view, false);
  assert.equal(game.travel, null);
  game.update(view, true);
  const trip = game.travel;
  assert.ok(trip);
  game.update(structuredClone(view), true);
  assert.equal(game.travel, trip);
  await game.choose(game.layout.portals[0]);
  assert.deepEqual(sent, []);
  game.travelFrame(100);
  assert.equal(game.travel, null);
  assert.deepEqual(sent, []);
  game.update(view, true);
  assert.equal(game.travel, null);
  await game.choose(game.layout.portals[0]);
  assert.deepEqual(sent, [view.inputs[0]]);
});

test('the real renderer refreshes changed options, NPCs and scene placement', t => {
  const {game, view, builds} = rendererHarness(t);
  game.update(view, true);
  game.finishTravel();
  const changed = structuredClone(view);
  changed.scene.choices[0].text = 'Read the new map';
  game.update(changed, true);
  assert.equal(builds.length, 2);
  assert.equal(game.layout.portals[0].label, 'Read the new map');
  assert.equal(game.travel, null);
  changed.environment.scenes.find(s => s.scene === changed.scene.id).place = 1;
  changed.environment.scenes.find(s => s.scene === changed.scene.id).npcs = ['New guide'];
  game.update(changed, true);
  assert.equal(game.layout.place.id, 1);
  assert.ok(game.travel);
  assert.equal(builds.length, 3);
  assert.ok(distance(game.travel.route.arrival, game.layout.place) < 10);
  game.cancelTravel();
  game.update(changed, true);
  assert.equal(game.travel, null); // Manual takeover is retained across polls.
});
