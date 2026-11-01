import { test } from 'node:test';
import assert from 'node:assert/strict';
import { playbackView, reportDuration } from '../web/playback.js';

const before = {
  phase: 'fight', scene: { id: 4 }, character: { hp: 11 },
  fight: { round: 1, hero: { hp: 11, alive: true }, foes: [{ hp: 8, alive: true }], maneuvers: [] },
  inputs: [], reports: [{ fightStarts: { hero: { hp: 11 }, foes: [{ hp: 8 }] } }],
};
const damage = { damage: { defender: null, hp: 6, injury: 5, faces: [5] } };

test('HP and deaths follow the displayed reports rather than leaking the final response', () => {
  const after = { ...before, character: { hp: 6 }, reports: [...before.reports, { round: { n: 2 } }, damage] };
  assert.equal(playbackView(before, after, 1).character.hp, 11);
  assert.equal(playbackView(before, after, 2).character.hp, 11);
  assert.equal(playbackView(before, after, 2).fight.round, 2);
  assert.equal(playbackView(before, after, 3).character.hp, 6);
  assert.equal(before.fight.hero.hp, 11);
});

test('a won fight stays visible until the scene report, with no stale command enabled', () => {
  const after = { ...before, phase: 'scene', scene: { id: 5, choices: [] }, fight: null,
    reports: [...before.reports, damage, 'fightWon', { scene: { id: 5, ending: false } }] };
  const presented = playbackView(before, after, 2);
  assert.equal(presented.phase, 'fight');
  assert.equal(presented.character.hp, 6);
  assert.deepEqual(presented.inputs, []);
  assert.equal(playbackView(before, after, 4).scene.id, 5);
});

test('visible dice have bounded playback while metadata introduces no hidden pauses', () => {
  const round = [{ round: { n: 2 } }, { attack: {} }, { dodge: {} }, damage, { maneuver: {} }];
  assert.equal(reportDuration({ round: {} }), 0);
  assert.equal(reportDuration(damage, 0), 0);
  const total = round.reduce((sum, r) => sum + reportDuration(r), 0);
  assert.ok(total <= 2000);
  assert.equal(reportDuration(damage, 2), reportDuration(damage, 1) / 2);
});
