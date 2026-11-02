// The pace at which the Scene text unfolds, like a story being told. Display only: it never
// changes what the text says or what the Player can choose.

/** The pause after each word, in milliseconds. */
export const WORD_MS = 75;
/** The extra pause after a word that ends a sentence. */
export const SENTENCE_MS = 450;
/** The extra pause after a word that ends with a comma, semicolon, colon, or dash. */
export const CLAUSE_MS = 180;

/** Split `text` into words and spaces. Each word gets `at`, the time in milliseconds after the
 * start when it shows. Spaces keep their place, so the joined parts give back `text` exactly. */
export function storyTimeline(text) {
  const parts = [];
  let at = 0;
  for (const piece of text.split(/(\s+)/)) {
    if (!piece) continue;
    if (/^\s+$/.test(piece)) { parts.push({ space: piece }); continue; }
    parts.push({ word: piece, at });
    at += WORD_MS;
    if (/[.!?…]["'”’)]*$/.test(piece)) at += SENTENCE_MS;
    else if (/[,;:—–]["'”’)]*$/.test(piece)) at += CLAUSE_MS;
  }
  return parts;
}

/** The time in milliseconds until the last word of `text` shows. */
export const storyLength = text => storyTimeline(text).reduce((end, p) => p.word ? p.at : end, 0);
