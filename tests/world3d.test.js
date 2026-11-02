import { test } from 'node:test';
import assert from 'node:assert/strict';
import * as THREE from '../web/vendor/three.module.js';
import { SpatialGame } from '../web/world3d.js';

// Build the real ground of a world, without a WebGL renderer.
function terrainFor(environment) {
  const game = Object.create(SpatialGame.prototype);
  Object.assign(game, { scene: new THREE.Scene(), renderer: { shadowMap: {} }, root: { dataset: {} } });
  game.buildWorld({ adventure: 'Test', world: 'Test' }, environment);
  game.terrain.updateMatrixWorld(true);
  return game.terrain;
}

const top = mesh => new THREE.Box3().setFromObject(mesh).max.y;
const overlapXZ = (a, b) => {
  const p = new THREE.Box3().setFromObject(a), q = new THREE.Box3().setFromObject(b);
  return p.min.x < q.max.x && q.min.x < p.max.x && p.min.z < q.max.z && q.min.z < p.max.z;
};

// Two flat surfaces at the same height flicker (z-fighting). A river at the largest scale used to
// put its water top at the same height as a place pad, as at Matson's Ford in the built-in Adventure.
test('river water stays below every trail and place pad that it passes under, at every scale', () => {
  for (const scale of [50, 100, 200]) {
    const environment = {
      theme: 'forest',
      places: [{ id: 0, name: 'Ford', kind: 'village', x: 0, z: 0 }, { id: 1, name: 'Bank', kind: 'camp', x: 40, z: 0 }],
      paths: [{ fromPlace: 0, toPlace: 1 }],
      props: [{ kind: 'river', x: 5, z: 0, scale, heading: 0 }],
      scenes: [],
    };
    const terrain = terrainFor(environment);
    const river = terrain.children.find(c => c.isGroup);
    const water = river.children;
    const ground = terrain.children.filter(c => c.isMesh && c.geometry.type === 'BoxGeometry' && top(c) > 0);
    assert.ok(water.length > 1 && ground.length >= 3);
    let crossings = 0;
    for (const w of water) for (const g of ground) if (overlapXZ(w, g)) {
      crossings++;
      assert.ok(top(w) <= top(g) - 0.001, `scale ${scale}: water top ${top(w)} is not below ${top(g)}`);
    }
    assert.ok(crossings > 0);
  }
});
