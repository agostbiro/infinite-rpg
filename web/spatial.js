// The spatial adapter contains no game rules, dice, or destination inference.
// Each interaction carries an input offered by the current Lean view, unchanged.

export function inputKey(value) {
  if (Array.isArray(value)) return '[' + value.map(inputKey).join(',') + ']';
  if (value && typeof value === 'object') {
    return '{' + Object.keys(value).sort().map(k => JSON.stringify(k) + ':' + inputKey(value[k])).join(',') + '}';
  }
  return JSON.stringify(value);
}

/** One spatial selector per offered input. Labels never determine an input. */
export function portalsForView(view) {
  if (!view || !['scene', 'fight'].includes(view.phase)) return [];
  const offered = new Set(view.inputs.map(inputKey));
  const candidates = view.phase === 'scene'
    ? (view.scene?.choices || []).filter(c => c.input !== null).map(c => ({ label: c.text, input: c.input, kind: 'choice' }))
    : (view.fight?.maneuvers || []).flatMap(m => m.options.map(o => ({
      label: m.label + (m.attacks && o.target !== null ? ' · ' + (view.fight.foes[o.target]?.name || 'Target') : ''),
      detail: m.help, input: o.input, kind: m.attacks ? 'attack' : 'defense',
    })));
  const seen = new Set();
  const portals = candidates.filter(p => offered.has(inputKey(p.input))).map(p => {
    const key = inputKey(p.input);
    if (seen.has(key)) throw new Error('The server offered the same spatial input twice.');
    seen.add(key);
    return { ...p, key, visual: appearanceFor(p, view) };
  });
  if (seen.size !== offered.size) throw new Error('The spatial view does not represent every offered input.');
  return portals;
}

/** Cosmetic interpretation only. These hints never create commands or outcomes. */
export function appearanceFor(option) {
  const text = option.label.toLowerCase();
  if (option.kind === 'attack') return { type: 'sword' };
  if (option.kind === 'defense') return { type: 'shield' };
  if (/talk|speak|ask|tale|chatter|diploma|parler|discut|convainc/.test(text)) return { type: 'person' };
  if (/climb|escalad|grimp|ladder|échelle/.test(text)) return { type: 'ladder' };
  if (/stair|escalier/.test(text)) return { type: 'stairs' };
  if (/ferry|boat|barque|bateau/.test(text)) return { type: 'boat' };
  if (/swim|nage|nager|river|rivière|causeway|wade/.test(text)) return { type: 'water' };
  if (/window|fenêtre/.test(text)) return { type: 'window' };
  if (/door|lock|porte|serrure/.test(text)) return { type: 'door' };
  if (/map|ledger|notebook|survey|contract|document|record|evidence|compare/.test(text)) return { type: 'table' };
  if (/cloud|weather|nuage|ciel|observer|look|inspect|examin/.test(text)) return { type: 'lookout' };
  if (/chest|coffre|search|fouill|take|pick up|ramass/.test(text) && !/way|path|route/.test(text)) return { type: 'chest' };
  if (/lamp|light|lantern|phare|allum/.test(text)) return { type: 'lantern' };
  if (/fight|attack|sword|combat|épée|attaqu|défier|sabre/.test(text)) return { type: 'sword' };
  if (/rest|sleep|wait|repos|dormir|attendre/.test(text)) return { type: 'camp' };
  // A traversable trail is a safe visual fallback for unfamiliar narrative text.
  return { type: 'path' };
}

/** Narrative figures are decoration; actual combatants come from the engine. */
export function figuresForView(view) {
  if (view.fight) return view.fight.foes.map((foe, index) => ({ ...foe, index, combat: true }));
  const cast = view.environment?.scenes.find(s => s.scene === view.scene?.id)?.npcs;
  if (Array.isArray(cast)) return cast.map((name, index) => ({name, index, species:'person', alive:true, combat:false}));
  const text = view.scene?.text || '';
  const figures = [];
  const add = (name, species = 'person') => {
    if (!figures.some(f => f.name === name || f.name.endsWith(' ' + name))) figures.push({ name, species, alive: true, combat: false, index: figures.length });
  };
  // Recognize named subjects rather than every capitalized place or mentioned person.
  for (const match of text.matchAll(/\b((?:(?:Old )?Mother|Father|Captain|Sir|Lady|Grey) [A-Z][a-z]+)\b/g)) add(match[1]);
  for (const match of text.matchAll(/(?:^|\s)(\p{Lu}\p{Ll}+(?: \p{Lu}\p{Ll}+)?) (?:stands|sits|waits|says|asks|whispers|smiles|hammers|dit|attend|demande|observe|examine|compare|reconnaît|intervient)\b/gu)) {
    if (!/^(?:The|You|He|She|Le|La|Il|Elle)$/.test(match[1])) add(match[1]);
  }
  if (/\bstranger\b/i.test(text)) add('The stranger');
  if (/\b(?:grey |gray )?wolf\b/i.test(text)) add('Grey wolf', 'wolf');
  if (/\b(?:goblin|gobelin)\b/i.test(text)) add('Goblin', 'goblin');
  if (/\b(?:guard|garde)\b/i.test(text)) add('Guard');
  if (/\b(?:merchant|marchand)\b/i.test(text)) add('Merchant');
  if (/\b(?:villager|villageois)\b/i.test(text)) add('Villager');
  if (!figures.length && /\b(?:he|she) says\b|\b(?:man|woman|homme|femme|personnage)\b/i.test(text)) add('Traveller');
  return figures;
}

/** The first gate crossed by a movement segment, including a large frame step. */
export function crossedPortal(from, to, portals, radius = 0.72) {
  const dx = to.x - from.x;
  const dz = to.z - from.z;
  const a = dx * dx + dz * dz;
  if (a === 0) return null;
  let first = null;
  let firstTime = Infinity;
  for (const p of portals) {
    const ox = from.x - p.x;
    const oz = from.z - p.z;
    const c = ox * ox + oz * oz - radius * radius;
    // A failed request must not retrigger until the player leaves and re-enters.
    if (c <= 0) continue;
    const b = 2 * (ox * dx + oz * dz);
    const discriminant = b * b - 4 * a * c;
    if (discriminant < 0) continue;
    const t = (-b - Math.sqrt(discriminant)) / (2 * a);
    if (t >= 0 && t <= 1 && t < firstTime) { first = p; firstTime = t; }
  }
  return first;
}

/** Visual variation only: this never participates in a logical transition. */
export function themeFor(view) {
  const text = (view.environment?.theme || [view.adventure, view.world].join(' ')).toLowerCase();
  if (/space|starship|station|robot|cyber|galax/.test(text)) return { name: 'Astral', sky: 0x111629, ground: 0x283347, stone: 0x536077, glow: 0x78d9e8, nature: false };
  if (/desert|désert|sand|sable|dune|pyramid|égypte|egypte|egypt/.test(text)) return { name: 'Dunes', sky: 0x829ba2, ground: 0xc3a063, stone: 0xd3b77e, glow: 0xffd783, nature: false };
  if (/shire|forest|wood|garden|acorn|hobbit|grove/.test(text)) return { name: 'Woodland', sky: 0x526f71, ground: 0x425c45, stone: 0x75816a, glow: 0xeac878, nature: true };
  if (/snow/.test(text)) return { name: 'Snow', sky: 0x9cbcc8, ground: 0xdde6e8, stone: 0x8f9ba6, glow: 0x95d9ff, nature: false };
  if (/city/.test(text)) return { name: 'City', sky: 0x9db0bd, ground: 0x77787a, stone: 0xb5b1a8, glow: 0xf4cb88, nature: false };
  return { name: 'Coast', sky: 0x3a5367, ground: 0x535b61, stone: 0x7d888a, glow: 0xeec582, nature: false };
}
