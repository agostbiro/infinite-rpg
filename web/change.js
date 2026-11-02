// The words the page shows for a live change. The server sends a `changeApplied` Report when it puts
// a change in play (Rpg/Report.lean). This module only turns that Report into text. It never
// decides what a change does.

/** The kind of a Report, such as "attack". Reports with no data are plain strings. */
const kindOf = (r) => (typeof r === 'string' ? r : Object.keys(r)[0]);

/** The condition of a rule, in plain words. */
const TRIGGERS = {
  always: 'always', wounded: 'at half HP or less', desperate: 'at one third HP or less',
  reckless: 'while using All-Out Attack', guarding: 'while using All-Out Defense',
  againstReckless: 'against All-Out Attack', againstGuarding: 'against All-Out Defense',
  againstFlame: 'against a flamethrower',
};

/** The numbers of a rule in plain words, such as "Enemies, at half HP or less: +2 to hit." */
export function ruleEffect(rule) {
  const signed = (n) => (n > 0 ? '+' + n : String(n));
  const effects = [];
  if (rule.hitBonus) effects.push(signed(rule.hitBonus) + ' to hit');
  if (rule.damageBonus) effects.push(signed(rule.damageBonus) + ' damage');
  if (rule.armorBonus) effects.push('+' + rule.armorBonus + ' armor');
  const who = rule.side === 'hero' ? 'You' : 'Enemies';
  return who + ', ' + (TRIGGERS[rule.trigger] || rule.trigger) + ': ' + effects.join(', ') + '.';
}

/** The tag of a rule in "Rules of this world", from its `origin`, or null for a rule of the
 * Adventure itself. */
export function originTag(rule) {
  if (rule.origin === 'requested') return 'Your change';
  if (rule.origin === 'counter') return "The world's answer";
  return null;
}

/** The damage and attack of a weapon, such as "2d+1 cutting · attack 14". */
const gearLine = (g) => g.damage + ' · attack ' + g.attack;

/** What a change put in play, as text for the page.
 * - `title`: the main line, such as "You received: Laser Sabre", "New rule: Iron Skin", or
 *   "The road ahead changed".
 * - `details`: lines under the title: the numbers of the gift or rule, and what it replaced.
 * - `answers`: one `{ name, effect }` for each counter-rule.
 * - `road`: true if the change also adds or replaces Scenes. It names none of them. */
export function changeSummary(note) {
  const details = [];
  let title;
  if (note.equipment) {
    const g = note.equipment;
    title = 'You received: ' + g.name;
    details.push(gearLine(g));
    if (g.was && g.was.name !== g.name) details.push('Replaces your ' + g.was.name + ' (' + gearLine(g.was) + ')');
  }
  for (const rule of note.requested || []) {
    const line = 'New rule: ' + rule.name;
    if (title === undefined) title = line; else details.push(line);
    details.push(ruleEffect(rule));
  }
  const road = (note.scenes || 0) > 0;
  if (title === undefined) title = road ? 'The road ahead changed' : 'The world changed';
  else if (road) details.push('The road ahead changed.');
  const answers = (note.counter || []).map((rule) => ({ name: rule.name, effect: ruleEffect(rule) }));
  return { title, details, answers, road };
}

/** One sentence that says what a change put in play, such as "You received: Laser Sabre." */
export function changeSentence(note) {
  const s = changeSummary(note);
  const answers = s.answers.map((a) => a.name).join(', ');
  return s.title + '.' + (answers ? ' The world answers: ' + answers + '.' : '');
}

/** `true` if `after` adds Reports to `before` and the new ones put a change in play. Then the page
 * plays the new Reports, so the Player sees the change. Else it can show `after` at once. */
export function addsChange(before, after) {
  if (!before || !after || after.length <= before.length) return false;
  for (let i = 0; i < before.length; i++) {
    if (JSON.stringify(before[i]) !== JSON.stringify(after[i])) return false;
  }
  return after.slice(before.length).some((r) => kindOf(r) === 'changeApplied');
}

/** The note of the change if the last of the first `shown` Reports is a change, else null. The page
 * marks the change as new until the next Report, that is, until the next input. */
export function freshChange(reports, shown = reports.length) {
  const last = reports[shown - 1];
  return last && kindOf(last) === 'changeApplied' ? last.changeApplied : null;
}

/** The gear chip of the 3D view: the weapon and its damage, and `isNew` while a change that gave it
 * is the last Report. */
export function gearChip(character, reports, shown = reports.length) {
  const fresh = freshChange(reports, shown);
  return {
    text: character.weapon + ' · ' + character.damage,
    isNew: !!(fresh && fresh.equipment),
  };
}
