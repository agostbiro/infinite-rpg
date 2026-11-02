// The move to the next Scene is presentation only. This module has no commands or network access.
import { facingVectors } from './environment.js';

const distance = (a, b) => Math.hypot(b.x - a.x, b.z - a.z);
const point = p => ({ x: p.x, z: p.z });
const clamp01 = t => Math.max(0, Math.min(1, t));
/** Slow at the start and at the end, fast in the middle. */
const ease = t => t < 0.5 ? 2 * t * t : 1 - (2 - 2 * t) ** 2 / 2;

/** A move shorter than this many metres, with a turn smaller than this many radians, is a glide.
 * Any other move is a fade to black, so the Player does not see a long move or a fast turn. */
export const GLIDE_LIMIT = 12;
export const GLIDE_TURN_LIMIT = 1.2;
/** The time of a glide and of a fade, in seconds. Both are under one second. */
export const GLIDE_SECONDS = 0.6;
export const FADE_SECONDS = 0.7;
/** The camera looks a little down, as when the game starts. */
export const DEFAULT_PITCH = -0.04;

/** Where the Player stands when a Scene starts: 5 m in front of its points, out of their reach. */
export function arrivalForLayout(layout) {
  const { forward } = facingVectors(layout.facing || 0);
  return { x: layout.center.x - forward.x * 2, z: layout.center.z - forward.z * 2 };
}

/** The smallest turn from angle `from` to angle `to`, in radians, from -π to π. */
export function shortestTurn(from, to) {
  return Math.atan2(Math.sin(to - from), Math.cos(to - from));
}

/** Plan the move of the camera from `from` to `to`, to look at `targetYaw`. A glide turns the
 * short way while it moves. A fade turns while the screen is black. So the view never jumps. */
export function planTransition(from, to, yaw, pitch, targetYaw = 0) {
  const turn = shortestTurn(yaw, targetYaw);
  const fade = distance(from, to) >= GLIDE_LIMIT || Math.abs(turn) > GLIDE_TURN_LIMIT;
  return {
    kind: fade ? 'fade' : 'glide', duration: fade ? FADE_SECONDS : GLIDE_SECONDS,
    from: point(from), to: point(to),
    fromYaw: yaw, turn, fromPitch: pitch, toPitch: DEFAULT_PITCH,
  };
}

/** The camera `t` seconds into a transition. `fade` is 0 for a clear view and 1 for black.
 * A fade moves the Player only while the screen is black. */
export function transitionAt(plan, t) {
  const s = clamp01(t / plan.duration);
  // A glide eases all the way. A fade changes the camera at once, in the middle, when it is black.
  const k = plan.kind === 'glide' ? ease(s) : Number(s >= 0.5);
  const camera = {
    position: { x: plan.from.x + (plan.to.x - plan.from.x) * k, z: plan.from.z + (plan.to.z - plan.from.z) * k },
    yaw: plan.fromYaw + plan.turn * k,
    pitch: plan.fromPitch + (plan.toPitch - plan.fromPitch) * k,
    done: s >= 1,
  };
  // A fade is black for its middle third: fade out, move, fade in.
  const fade = plan.kind === 'glide' ? 0 : clamp01((1 - Math.abs(2 * s - 1)) * 1.5);
  return { ...camera, fade };
}
