import { test } from 'node:test';
import assert from 'node:assert/strict';
import * as THREE from '../web/vendor/three.module.js';
import { SpatialGame } from '../web/world3d.js';
import { heldWeapon } from '../web/gear.js';

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

// The weapon in the hand is built from the shape that gear.js picks, out of simple meshes.
test('a held Laser Sabre has a glowing blade, and a plain broadsword has none', () => {
  const game = Object.create(SpatialGame.prototype);
  const glows = group => {
    const found = [];
    group.traverse(o => { if (o.isMesh && o.material.isMeshBasicMaterial) found.push(o); });
    return found;
  };
  const sabre = game.buildHeld(heldWeapon('broadsword', 'Laser Sabre'));
  const plain = game.buildHeld(heldWeapon('broadsword', 'Broadsword'));
  assert.ok(glows(sabre).length >= 2);
  assert.equal(glows(plain).length, 0);
  assert.ok(plain.children.length >= 4);
  // The blade points up from the grip, and the sword is under 1.2 m long.
  const size = new THREE.Box3().setFromObject(sabre).getSize(new THREE.Vector3());
  assert.ok(size.y > 0.7 && size.y < 1.2, String(size.y));
  // Fists show no weapon.
  assert.equal(game.buildHeld(heldWeapon('punch', 'fists')).children.length, 0);
});
