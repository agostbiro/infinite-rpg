// Presentation geometry only. Story commands always come from the current Lean view.
export const WORLD_BOUND = 115;
export const propRadius = p => Math.ceil(({ pyramid: 12, house: 5, river: 0 }[p.kind] ?? 3) * p.scale / 100);

export function segmentDistance(p, a, b) {
  const dx = b.x - a.x, dz = b.z - a.z;
  const t = Math.max(0, Math.min(1, ((p.x-a.x)*dx + (p.z-a.z)*dz) / (dx*dx+dz*dz || 1)));
  return Math.hypot(p.x-a.x-t*dx, p.z-a.z-t*dz);
}

/** The world map of the view, or a default map of four places when the Adventure has none. */
export function environmentFor(view) {
  if (view.environment) return view.environment;
  const text = [view.adventure, view.world].join(' ').toLowerCase();
  const theme = /egypt|desert|nile/.test(text) ? 'desert'
    : /forest|shire|wood/.test(text) ? 'forest' : /space|star/.test(text) ? 'space' : 'coast';
  return {
    theme,
    places: [
      { id: 0, name: 'Base Camp', kind: 'camp', x: -30, z: 30 },
      { id: 1, name: 'Trading Post', kind: 'market', x: 30, z: 30 },
      { id: 2, name: 'Old Ruins', kind: 'ruins', x: 30, z: -30 },
      { id: 3, name: 'The Outlook', kind: 'outpost', x: -30, z: -30 },
    ],
    paths: [[0,1],[1,2],[2,3],[3,0]].map(([fromPlace,toPlace]) => ({fromPlace,toPlace})),
    props: [
      {kind: theme === 'forest' ? 'tree' : 'rock', x: 0, z: 0, scale: 150, heading: 0},
      {kind: theme === 'desert' ? 'pyramid' : 'house', x: -65, z: -65, scale: 150, heading: 0},
    ],
    scenes: [],
  };
}

export function placeForScene(environment, sceneId) {
  const id = environment.scenes.find(s => s.scene === sceneId)?.place;
  const place = environment.places.find(p => p.id === id);
  if (environment.scenes.length && !place) throw new Error('The current scene has no valid place in this world.');
  return place || environment.places[Math.floor((sceneId || 0) / 4) % environment.places.length];
}

/** Stable event positions within the checked clear area, distinct from its centre. */
export function eventAnchorForScene(environment, sceneId) {
  const place = placeForScene(environment, sceneId);
  const localScenes = environment.scenes.filter(s => s.place === place.id);
  const slot = Math.max(0, localScenes.findIndex(s => s.scene === sceneId));
  const angle = (slot % 8) * Math.PI / 4;
  return {x: place.x + 2.8*Math.sin(angle), z: place.z + 2.8*Math.cos(angle)};
}

/** The unit vectors forward and right for a camera that turns by `yaw` (0 looks down -z). */
export function facingVectors(yaw) {
  return { forward: { x: -Math.sin(yaw), z: -Math.cos(yaw) }, right: { x: Math.cos(yaw), z: -Math.sin(yaw) } };
}

/** Put the points of a Scene in rows in front of `center`, as seen from the direction `facing`.
 * In a Scene the rows start 3 m north of the event anchor. In a Fight (`anchor` is the Player)
 * the foes stand 6 m in front of the Player, so the camera does not need to turn. */
export function worldLayout(points, place, anchor = null, eventAnchor = null, facing = 0) {
  const center = anchor || eventAnchor || place;
  const { forward, right } = facingVectors(facing);
  const ahead = anchor ? 6 : 3, spacing = anchor ? 2.4 : 3.6;
  return {
    bound: WORLD_BOUND, place, center, facing,
    points: points.map((p, i) => {
      const row = Math.floor(i / 4), inRow = Math.min(points.length - row * 4, 4);
      // A back row with the same parity as the front row moves half a step, into the gaps.
      const shift = row > 0 && inRow % 2 === Math.min(points.length, 4) % 2 ? 0.5 : 0;
      const side = ((i % 4) - (inRow - 1) / 2 + shift) * spacing;
      const depth = ahead + row * 3.6;
      return { ...p, index: i,
        x: center.x + forward.x * depth + right.x * side,
        z: center.z + forward.z * depth + right.z * side };
    }),
  };
}

/** Place scenery uses the same model vocabulary as authored props. Keep trails clear. */
export function sceneryFor(environment) {
  const props = environment.props.map(p => ({ ...p }));
  const clear = p => environment.paths.every(path => {
    const a = environment.places.find(q => q.id === path.fromPlace);
    const b = environment.places.find(q => q.id === path.toPlace);
    return segmentDistance(p, a, b) >= propRadius(p) + 2;
  }) && environment.places.every(q => Math.hypot(p.x-q.x,p.z-q.z) >= propRadius(p)+10);
  for (const place of environment.places) {
    const kind = ({camp:'tent',harbour:'house',village:'house',market:'tent',ruins:'column',temple:'column',forest:'tree',outpost:'tent'})[place.kind];
    for (const [dx,dz] of [[-13,-13],[13,-13],[-13,13],[13,13]]) {
      const p = { kind, x: place.x+dx, z:place.z+dz, scale:100, heading:0 };
      if (clear(p)) props.push(p);
    }
  }
  return props;
}

/** Slide around solid scenery, in small steps so a slow frame cannot cross a wall. */
export function moveInWorld(position, dx, dz, obstacles, bound = WORLD_BOUND) {
  const steps = Math.max(1, Math.ceil(Math.hypot(dx,dz) / 0.3));
  let {x,z} = position;
  const clamp = n => Math.max(-bound, Math.min(bound,n));
  const free = (x,z) => obstacles.every(o => Math.hypot(x-o.x,z-o.z) >= o.radius+0.4);
  for (let i=0;i<steps;i++) {
    const nx=clamp(x+dx/steps), nz=clamp(z+dz/steps);
    if (free(nx,nz)) { x=nx; z=nz; }
    else { if (free(nx,z)) x=nx; if (free(x,nz)) z=nz; }
  }
  return {x,z};
}
