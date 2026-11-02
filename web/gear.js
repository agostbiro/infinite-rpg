// The look of the weapon in the Player's hand in the 3D view. This module only picks a shape and a
// style from what the server sends: the weapon's kind (its rule type, such as "broadsword") and its
// name. It never decides what the weapon does.

/** The shape for each weapon kind. The kinds are the JSON names of the weapons in Lean
 * (`Weapon.key` in Rpg/Live.lean). A punch has no weapon to draw. */
const SHAPES = {
  broadsword: 'sword',
  largeKnife: 'knife',
  quarterstaff: 'staff',
  flamethrower: 'sprayer',
  punch: null,
};

/** A word in the name that makes a pole into a spear: it gets a point at the top. */
const SPEAR = /\b(pike|spear|lance|glaive|halberd|trident|javelin|partisan)/i;

/** Words in the name that give a glowing energy blade. Each one is a whole word, so "Legion" is not
 * "ion" and "Lightfoot" is not "light". */
const ENERGY = /\b(laser|light|lightsaber|lightsabre|plasma|energy|ion|photon|beam|lumen)\b/i;
/** Words in the name that give a fire glow. They can start a longer word, such as "Firebrand". */
const FIRE = /\b(flame|fire|cinder|ember|blaze|inferno|burning)/i;
/** Words in the name that give a pale ice blue. */
const ICE = /\b(ice|icy|frost|frozen|glacial|glacier|snow|rime)/i;

/** Colors that the name can ask for, as 0xRRGGBB. The first match in this list wins. */
const COLORS = [
  [/\b(red|crimson|scarlet|ruby|blood)/i, 0xff3b30],
  [/\b(blue|azure|sapphire|cobalt)/i, 0x3d8bff],
  [/\b(green|emerald|jade)/i, 0x3ee66b],
  [/\b(purple|violet|amethyst)/i, 0xb05cff],
  [/\b(gold|golden|yellow|amber)/i, 0xffd23d],
  [/\b(white|silver|pale)/i, 0xf2f6ff],
  [/\b(orange)/i, 0xff8a2a],
  [/\b(cyan|teal)/i, 0x3de8ff],
];

/** The energy color when the name has no color word: each energy word has its own. */
const ENERGY_DEFAULT = { laser: 0xff3b30, plasma: 0xb05cff, ion: 0x3de8ff };

const FIRE_COLOR = 0xff7a1f;
const ICE_COLOR = 0xbfe6ff;
const METAL_COLOR = 0xc9ced6;
const WOOD_COLOR = 0x8a5a33;

/** The color word in a name, or null. */
export function colorFromName(name) {
  for (const [pattern, color] of COLORS) if (pattern.test(name)) return color;
  return null;
}

/** How to draw the weapon in the hand: `shape` ("sword", "knife", "staff", "spear", "sprayer", or
 * null for no weapon), `finish` ("energy", "fire", "ice", "metal", or "wood"), `glow` (true for a
 * glowing blade or tip), and `color` (0xRRGGBB). An unknown kind is drawn as a sword. */
export function heldWeapon(kind, name = '') {
  const known = Object.prototype.hasOwnProperty.call(SHAPES, kind);
  let shape = known ? SHAPES[kind] : 'sword';
  if (shape === null) return { shape: null, finish: 'metal', glow: false, color: METAL_COLOR };
  if (shape === 'staff' && SPEAR.test(name)) shape = 'spear';
  const energy = name.match(ENERGY);
  if (energy) {
    const word = energy[1].toLowerCase();
    const color = colorFromName(name) ?? ENERGY_DEFAULT[word] ?? 0x5fb4ff;
    return { shape, finish: 'energy', glow: true, color };
  }
  if (FIRE.test(name)) return { shape, finish: 'fire', glow: true, color: FIRE_COLOR };
  if (ICE.test(name)) return { shape, finish: 'ice', glow: false, color: ICE_COLOR };
  const pole = shape === 'staff';
  return { shape, finish: pole ? 'wood' : 'metal', glow: false, color: pole ? WOOD_COLOR : METAL_COLOR };
}
