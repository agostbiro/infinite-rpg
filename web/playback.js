// Presentation of authoritative reports; this module never rolls dice or selects inputs.
export const reportKind = report => typeof report === 'string' ? report : Object.keys(report)[0];
export const reportData = report => typeof report === 'string' ? {} : report[reportKind(report)];

/** Keep the displayed scene and HP at the report being shown, not at the final server reply. */
export function playbackView(before, after, shown) {
  if (!before || shown >= after.reports.length) return after;
  let phase = before.phase, scene = before.scene;
  let hp = before.character.hp;
  let fight = before.fight ? structuredClone(before.fight) : null;
  for (const report of after.reports.slice(before.reports.length, shown)) {
    const kind = reportKind(report), data = reportData(report);
    if (kind === 'scene') {
      scene = after.scene?.id === data.id ? after.scene : { ...data, choices: [] };
      phase = data.ending ? 'ended' : 'scene';
      fight = null;
    } else if (kind === 'fightStarts') {
      phase = 'fight';
      fight = {
        hero: { ...data.hero, alive: data.hero.hp > 0 },
        foes: data.foes.map(foe => ({ ...foe, alive: foe.hp > 0 })),
        maneuvers: after.fight?.maneuvers || [], round: 1,
      };
      hp = data.hero.hp;
    } else if (kind === 'round' && fight) fight.round = data.n;
    else if (kind === 'damage') {
      if (data.defender === null) hp = data.hp;
      const target = data.defender === null ? fight?.hero : fight?.foes[data.defender];
      if (target) { target.hp = data.hp; target.alive = data.hp > 0; }
    } else if (kind === 'died') phase = 'dead';
  }
  const current = phase === after.phase && scene?.id === after.scene?.id;
  return { ...after, phase, scene, fight, character: { ...after.character, hp },
    inputs: current ? after.inputs : [], reports: after.reports.slice(0, shown) };
}

/** Cosmetic timing is short and applies only to reports the player can actually see. */
export function reportDuration(report, speed = 1, spatial = true) {
  const kind = reportKind(report);
  const duration = ['attack', 'dodge', 'successRoll'].includes(kind) ? 700
    : kind === 'damage' ? 550
    : ['fightStarts', 'fightWon', 'died', 'scene'].includes(kind) ? 280
    : spatial ? 0 : 180;
  return speed === 0 ? 0 : duration / speed;
}
