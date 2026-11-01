// Automatic travel is presentation only. This module has no commands or network access.
import { segmentDistance, moveInWorld } from './environment.js';

const distance = (a, b) => Math.hypot(b.x - a.x, b.z - a.z);
const point = p => ({ x: p.x, z: p.z });

/** Stop five metres in front of the options, outside their contact and E ranges. */
export function arrivalForLayout(layout) {
  return { x: layout.center.x, z: layout.center.z + 2 };
}

/** Use the current world's undirected paths, with a clear approach from the player. */
export function planTravel(environment, position, layout, obstacles) {
  const arrival = arrivalForLayout(layout);
  const clear = (a, b) => obstacles.every(o => segmentDistance(o, a, b) >= o.radius + 0.45);
  if (!clear(arrival, arrival)) return null;
  // Movement inside the destination's clear area needs no trip via its centre.
  if (distance(position, layout.place) < 10 && clear(position, arrival)) {
    return { arrival, waypoints: [arrival], length: distance(position, arrival) };
  }
  const nodes = environment.places.map(point);
  const indices = new Map(environment.places.map((p, i) => [p.id, i]));
  const target = indices.get(layout.place.id);
  if (target === undefined || !clear(nodes[target], arrival)) return null;
  const edges = nodes.map(() => []);
  const connect = (i, j) => {
    const length = distance(nodes[i], nodes[j]);
    edges[i].push([j, length]); edges[j].push([i, length]);
  };
  for (const path of environment.paths) {
    const i = indices.get(path.fromPlace), j = indices.get(path.toPlace);
    if (i === undefined || j === undefined || !clear(nodes[i], nodes[j])) continue;
    connect(i, j);
    // A player exploring between places can rejoin the closest part of a trail.
    const a = nodes[i], b = nodes[j], dx = b.x - a.x, dz = b.z - a.z;
    const t = Math.max(0, Math.min(1, ((position.x-a.x)*dx + (position.z-a.z)*dz) / (dx*dx+dz*dz || 1)));
    const k = nodes.length;
    nodes.push({ x: a.x+t*dx, z: a.z+t*dz }); edges.push([]);
    connect(i, k); connect(k, j);
  }
  const entries = nodes.map((p, i) => ({ i, distance: distance(position, p) }))
    .filter(({ i }) => clear(position, nodes[i])).sort((a, b) => a.distance - b.distance);
  if (!entries.length) return null;
  const start = entries[0].i;
  const costs = nodes.map(() => Infinity), previous = nodes.map(() => -1), visited = new Set();
  costs[start] = 0;
  while (visited.size < nodes.length) {
    let current = -1;
    for (let i = 0; i < nodes.length; i++) {
      if (!visited.has(i) && Number.isFinite(costs[i]) && (current < 0 || costs[i] < costs[current])) current = i;
    }
    if (current < 0 || current === target) break;
    visited.add(current);
    for (const [next, length] of edges[current]) {
      if (costs[current] + length < costs[next]) {
        costs[next] = costs[current] + length; previous[next] = current;
      }
    }
  }
  if (!Number.isFinite(costs[target])) return null;
  const waypoints = [];
  for (let i = target; i !== -1; i = previous[i]) waypoints.unshift(point(nodes[i]));
  waypoints.push(arrival);
  return { arrival, waypoints, length: entries[0].distance + costs[target] + distance(nodes[target], arrival) };
}

/** Follow the route using the same collisions as manual walking; never select an option. */
export function advanceTravel(position, route, index, budget, obstacles, bound) {
  let next = point(position);
  while (index < route.waypoints.length) {
    const target = route.waypoints[index], remaining = distance(next, target);
    if (remaining < 0.00001) { index++; continue; }
    if (budget <= 0) break;
    const step = Math.min(remaining, budget);
    const moved = moveInWorld(next, (target.x-next.x)*step/remaining, (target.z-next.z)*step/remaining, obstacles, bound);
    if (Math.abs(distance(next, moved) - step) > 0.00001) {
      return { position: moved, index, done: false, blocked: true };
    }
    next = moved; budget -= step;
    if (remaining <= step + 0.00001) { next = point(target); index++; }
  }
  return { position: next, index, done: index === route.waypoints.length, blocked: false };
}
