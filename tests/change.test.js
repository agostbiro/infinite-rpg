import { test } from 'node:test';
import assert from 'node:assert/strict';
import { ruleEffect, originTag, changeSummary, changeSentence, addsChange, freshChange, gearChip } from '../web/change.js';

const redcoats = { name: 'Rallying Redcoats', description: 'Wounded enemies close ranks.', side: 'foes',
  trigger: 'wounded', hitBonus: 2, damageBonus: 0, armorBonus: 0 };
const ironSkin = { name: 'Iron Skin', description: 'Your skin gains 2 armor.', side: 'hero',
  trigger: 'always', hitBonus: 0, damageBonus: 0, armorBonus: 2 };

/** A note as the server sends it (`changeNoteJson` in Rpg/View.lean). */
const sabre = {
  wish: 'Give me a laser sabre', summary: 'A sabre of light.', moment: 'Foes rally.',
  equipment: { name: 'Laser Sabre', damage: '2d+1 cutting', attack: 14, kind: 'broadsword',
    was: { name: 'Broadsword', damage: '1d+2 cutting', attack: 14 } },
  requested: [], counter: [redcoats], scenes: 0,
};

test('a rule effect says who gains what, and when', () => {
  assert.equal(ruleEffect(redcoats), 'Enemies, at half HP or less: +2 to hit.');
  assert.equal(ruleEffect(ironSkin), 'You, always: +2 armor.');
  assert.equal(ruleEffect({ ...redcoats, hitBonus: -1, damageBonus: 3 }), 'Enemies, at half HP or less: -1 to hit, +3 damage.');
});

test('a gift of equipment names the weapon, its numbers, what it replaces, and the answer', () => {
  const s = changeSummary(sabre);
  assert.equal(s.title, 'You received: Laser Sabre');
  assert.deepEqual(s.details, ['2d+1 cutting · attack 14', 'Replaces your Broadsword (1d+2 cutting · attack 14)']);
  assert.deepEqual(s.answers, [{ name: 'Rallying Redcoats', effect: 'Enemies, at half HP or less: +2 to hit.' }]);
  assert.equal(s.road, false);
  assert.equal(changeSentence(sabre), 'You received: Laser Sabre. The world answers: Rallying Redcoats.');
});

test('a rule-only change shows the new rule and its effect', () => {
  const s = changeSummary({ ...sabre, equipment: null, requested: [ironSkin] });
  assert.equal(s.title, 'New rule: Iron Skin');
  assert.deepEqual(s.details, ['You, always: +2 armor.']);
});

test('a Scenes-only change says the road changed, and names no Scene', () => {
  const s = changeSummary({ ...sabre, equipment: null, requested: [], scenes: 2 });
  assert.equal(s.title, 'The road ahead changed');
  assert.deepEqual(s.details, []);
  assert.equal(s.road, true);
  // With a gift as well, the road is one more line.
  assert.ok(changeSummary({ ...sabre, scenes: 1 }).details.includes('The road ahead changed.'));
});

test('a rule shows its origin as a tag', () => {
  assert.equal(originTag({ origin: 'requested' }), 'Your change');
  assert.equal(originTag({ origin: 'counter' }), "The world's answer");
  assert.equal(originTag({ origin: 'adventure' }), null);
  assert.equal(originTag({}), null);
});

test('new Reports play only when they add to the old ones and put a change in play', () => {
  const old = [{ scene: { id: 1 } }, { picked: { text: 'Go' } }];
  const change = { changeApplied: sabre };
  assert.equal(addsChange(old, [...old, change]), true);
  // No change in the new part: the page shows the view at once, as before.
  assert.equal(addsChange(old, [...old, { picked: { text: 'Again' } }]), false);
  // The old Reports are not a prefix (another game): no playback.
  assert.equal(addsChange(old, [{ scene: { id: 2 } }, { picked: { text: 'Go' } }, change]), false);
  assert.equal(addsChange(old, old), false);
  assert.equal(addsChange(null, [change]), false);
});

test('a change is fresh only while it is the last Report on screen', () => {
  const reports = [{ scene: { id: 1 } }, { changeApplied: sabre }];
  assert.equal(freshChange(reports), sabre);
  assert.equal(freshChange(reports, 1), null);
  assert.equal(freshChange([...reports, { picked: { text: 'Go' } }]), null);
  assert.equal(freshChange([]), null);
});

test('the gear chip names the weapon and its damage, and is new after a gift', () => {
  const character = { weapon: 'Laser Sabre', damage: '2d+1 cutting' };
  const reports = [{ scene: { id: 1 } }, { changeApplied: sabre }];
  assert.deepEqual(gearChip(character, reports), { text: 'Laser Sabre · 2d+1 cutting', isNew: true });
  assert.equal(gearChip(character, [...reports, 'fightWon']).isNew, false);
  // A rule-only change gives no new weapon, so the chip is not new.
  assert.equal(gearChip(character, [{ changeApplied: { ...sabre, equipment: null } }]).isNew, false);
});
