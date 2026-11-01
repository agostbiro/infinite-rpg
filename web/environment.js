// Presentation geometry only. Story commands always come from the current Lean view.
export const WORLD_BOUND = 115;
export const propRadius = p => Math.ceil(({ pyramid: 12, house: 5, river: 0 }[p.kind] ?? 3) * p.scale / 100);

export function segmentDistance(p, a, b) {
  const dx = b.x - a.x, dz = b.z - a.z;
  const t = Math.max(0, Math.min(1, ((p.x-a.x)*dx + (p.z-a.z)*dz) / (dx*dx+dz*dz || 1)));
  return Math.hypot(p.x-a.x-t*dx, p.z-a.z-t*dz);
}

/** Older saves have a generic connected world. New Wishes supply the full plan. */
export function environmentFor(view) {
  if (view.environment) return view.environment;
  const text = [view.adventure, view.world].join(' ').toLowerCase();
  const theme = /egypt|desert|nile|bonaparte/.test(text) ? 'desert'
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
  return environment.places.find(p => p.id === id)
    || environment.places[Math.floor((sceneId || 0) / 4) % environment.places.length];
}

/** Stable event positions within the checked clear area, distinct from its centre. */
export function eventAnchorForScene(environment, sceneId) {
  const place = placeForScene(environment, sceneId);
  const localScenes = environment.scenes.filter(s => s.place === place.id);
  const slot = Math.max(0, localScenes.findIndex(s => s.scene === sceneId));
  const angle = (slot % 8) * Math.PI / 4;
  return {x: place.x + 2.8*Math.sin(angle), z: place.z + 2.8*Math.cos(angle)};
}

/** Distinct objects in a clear square at the active location. No destination inference. */
export function worldLayout(portals, place, anchor = null, eventAnchor = null) {
  const center = anchor || eventAnchor || place;
  return {
    bound: WORLD_BOUND, place, center,
    spawn: { x: place.x, z: place.z + 5 },
    portals: portals.map((p, i) => ({
      ...p, index: i, angle: 0,
      x: center.x + ((i % 4) - (Math.min(portals.length, 4) - 1) / 2) * 3.6,
      z: anchor ? center.z + 2 + Math.floor(i / 4) * 3.6 : center.z - 3 - Math.floor(i / 4) * 3.6,
    })),
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
