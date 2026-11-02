import test from 'node:test';
import assert from 'node:assert/strict';
import { storyTimeline, storyLength, WORD_MS, SENTENCE_MS, CLAUSE_MS } from '../web/story.js';

// The opening Scene of the built-in Adventure.
const valleyForge = 'May 1778. The army has lived through a hard winter at Valley Forge. General Washington gives you 2,200 men and one task: watch the British in Philadelphia, and do not get caught. You are twenty years old, and some older officers think that you are too young for this. The road east passes the camp of the Pennsylvania militia.';

test('the unfolded story gives back the Scene text exactly', () => {
  for (const text of [valleyForge, '', 'One', '  two  spaces\nand a line  ']) {
    assert.equal(storyTimeline(text).map(p => p.word ?? p.space).join(''), text);
  }
});

test('words show in order, with longer pauses after sentences and clauses', () => {
  const words = storyTimeline('Halt, who goes there? Friend.').filter(p => p.word);
  assert.deepEqual(words.map(p => [p.word, p.at]), [
    ['Halt,', 0],
    ['who', WORD_MS + CLAUSE_MS],
    ['goes', 2 * WORD_MS + CLAUSE_MS],
    ['there?', 3 * WORD_MS + CLAUSE_MS],
    ['Friend.', 4 * WORD_MS + CLAUSE_MS + SENTENCE_MS]]);
  // "2,200" has a comma inside, not at the end, so it gets no clause pause.
  const number = storyTimeline('2,200 men').filter(p => p.word);
  assert.equal(number[1].at, WORD_MS);
});

test('a Scene unfolds in a few seconds, not too fast to feel told nor too slow to wait for', () => {
  const ms = storyLength(valleyForge);
  assert.ok(ms > 4000 && ms < 10000, `Valley Forge takes ${ms} ms`);
});
