import { test } from 'node:test';
import assert from 'node:assert/strict';
import { heldWeapon, colorFromName } from '../web/gear.js';

test('a Laser Sabre of the broadsword kind is a glowing sword', () => {
  const w = heldWeapon('broadsword', 'Laser Sabre');
  assert.equal(w.shape, 'sword');
  assert.equal(w.finish, 'energy');
  assert.equal(w.glow, true);
});

test('a plain Broadsword is a metal sword with no glow', () => {
  assert.deepEqual(heldWeapon('broadsword', 'Broadsword'), heldWeapon('broadsword', 'broadsword'));
  const w = heldWeapon('broadsword', 'Broadsword');
  assert.equal(w.shape, 'sword');
  assert.equal(w.finish, 'metal');
  assert.equal(w.glow, false);
});

test('an Ion Pike is a glowing spear on a staff, or a glowing sword on a broadsword', () => {
  const pole = heldWeapon('quarterstaff', 'Ion Pike');
  assert.equal(pole.shape, 'spear');
  assert.equal(pole.finish, 'energy');
  assert.equal(heldWeapon('broadsword', 'Ion Pike').shape, 'sword');
});

test('each weapon kind has its own shape, and a punch shows no weapon', () => {
  assert.equal(heldWeapon('largeKnife', 'Large knife').shape, 'knife');
  assert.equal(heldWeapon('quarterstaff', 'Quarterstaff').shape, 'staff');
  assert.equal(heldWeapon('quarterstaff', 'Quarterstaff').finish, 'wood');
  assert.equal(heldWeapon('flamethrower', 'Flamethrower').shape, 'sprayer');
  assert.equal(heldWeapon('punch', 'fists').shape, null);
  // A kind that the page does not know is drawn as a sword.
  assert.equal(heldWeapon('whip', 'Whip').shape, 'sword');
  assert.equal(heldWeapon(undefined, 'Sword').shape, 'sword');
});

test('a color word in the name sets the energy color', () => {
  assert.equal(heldWeapon('broadsword', 'Blue Laser Sabre').color, colorFromName('blue'));
  assert.equal(heldWeapon('broadsword', 'Green Plasma Blade').color, colorFromName('green'));
  assert.notEqual(heldWeapon('broadsword', 'Blue Laser Sabre').color, heldWeapon('broadsword', 'Red Laser Sabre').color);
  assert.equal(colorFromName('Broadsword'), null);
});

test('fire and ice words give their own finish', () => {
  assert.equal(heldWeapon('broadsword', 'Firebrand').finish, 'fire');
  assert.equal(heldWeapon('broadsword', 'Firebrand').glow, true);
  assert.equal(heldWeapon('largeKnife', 'Cinder Knife').finish, 'fire');
  assert.equal(heldWeapon('broadsword', 'Frost Blade').finish, 'ice');
  assert.equal(heldWeapon('broadsword', 'Ice Fang').finish, 'ice');
});

test('a keyword must be a whole word, so ordinary names stay metal', () => {
  for (const name of ['Legion Blade', 'Champion Sword', 'Lightfoot Dagger', 'Justice', 'Sabre of the Lion']) {
    assert.equal(heldWeapon('broadsword', name).finish, 'metal', name);
  }
});
