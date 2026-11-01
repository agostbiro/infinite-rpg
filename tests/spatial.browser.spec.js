import fs from 'node:fs';
import { test, expect } from '@playwright/test';
import { portalsForView } from '../web/spatial.js';
import {environmentFor,placeForScene,eventAnchorForScene,worldLayout} from '../web/environment.js';

// The test plays an Adventure from a recorded Wish (tests/fake-api/adventure-1.sse). There is none
// now, so the test is skipped. docs/follow-ups.md adds a recorded Wish back. The Scene names below are
// those of the earlier recorded Wish (The Silver Acorn); change them to the names of the new one.
const hasRecordedWish = fs.existsSync(new URL('./fake-api/adventure-1.sse', import.meta.url));

async function view(page) { return (await page.request.get('/api/view')).json(); }

async function settled(page) {
  await expect(page.locator('#world')).toBeVisible();
  // Report playback is cosmetic, and its real Skip control is part of the game.
  if (await page.locator('#skip').isVisible()) await page.locator('#skip').click();
  await expect(page.locator('body')).toHaveAttribute('data-state', 'ready', { timeout: 30000 });
  await expect(page.locator('#world')).toHaveAttribute('data-ready', 'true');
  await expect(page.locator('#world')).toHaveAttribute('data-travelling', 'false', { timeout: 15000 });
}

/** Reach a real interaction with keyboard events, never by changing app state. */
async function walkThrough(page, index) {
  await settled(page);
  const before = await view(page);
  const env=environmentFor(before);
  const place=placeForScene(env,before.scene.id);
  const gate=worldLayout(portalsForView(before),place,null,eventAnchorForScene(env,before.scene.id)).portals[index];
  expect(gate).toBeTruthy();
  const world = page.locator('#world');
  await page.locator('#world-canvas').focus();
  const nearText = await page.locator('#world-choice').textContent();
  if (await page.locator('#world-prompt').isVisible() && nearText === gate.label) {
    const request = page.waitForRequest(r => r.url().endsWith('/api/input') && r.method() === 'POST');
    await page.keyboard.press('e');
    expect((await request).postDataJSON()).toEqual({ revision: before.worldRevision, input: gate.input });
  } else {
    // Return to the inner floor before changing lanes. This never crosses a different gate.
    const moveAxis = async (axis, target) => {
      const initial = Number(await world.getAttribute('data-player-' + axis));
      if (Math.abs(target - initial) < 0.13) return;
      const sign = Math.sign(target - initial);
      const key = axis === 'x' ? (sign > 0 ? 'ArrowRight' : 'ArrowLeft') : (sign > 0 ? 'ArrowDown' : 'ArrowUp');
      await page.keyboard.down('Shift');
      await page.keyboard.down(key);
      try {
        await page.waitForFunction(({ axis, target, sign }) => {
          const p = Number(document.getElementById('world').getAttribute('data-player-' + axis));
          return sign * (p - target) >= -0.12;
        }, { axis, target, sign }, { timeout: 15000 });
      } finally {
        await page.keyboard.up(key); await page.keyboard.up('Shift');
      }
    };
    await moveAxis('z', place.z+5);
    await moveAxis('x', gate.x);
    const request = page.waitForRequest(r => r.url().endsWith('/api/input') && r.method() === 'POST');
    const key = gate.z < place.z+5 ? 'ArrowUp' : 'ArrowDown';
    await page.keyboard.down('Shift');
    await page.keyboard.down(key);
    try { expect((await request).postDataJSON()).toEqual({ revision: before.worldRevision, input: gate.input }); }
    finally { await page.keyboard.up(key); await page.keyboard.up('Shift'); }
  }
  await expect.poll(async () => (await view(page)).reports.length).toBeGreaterThan(before.reports.length);
  await settled(page);
  const after = await view(page);
  await expect(world).toHaveAttribute('data-portal-count', String(portalsForView(after).length));
  return after;
}

test('a Wish passes the real checks and is playable in 3D through a Fight to the end', async ({ page }, testInfo) => {
  test.skip(!hasRecordedWish, 'No recorded Wish in tests/fake-api. See docs/follow-ups.md: add back the fake-mode Wish.');
  const errors = [];
  const sent = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => { if (msg.type() === 'error') errors.push(msg.text()); });
  page.on('request', r => { if (r.url().endsWith('/api/input')) sent.push(r.postDataJSON()); });
  await page.goto('/');
  await page.locator('#new-open').click();
  await page.locator('#wish').fill('I love LOTR, give me an adventure set in the Shire');
  await page.locator('#wish-send').click();
  await expect(page.locator('#ready')).toBeVisible({ timeout: 120000 });
  await expect(page.locator('#progress-steps')).toContainText('passed');
  await page.locator('#play-now').click();
  await settled(page);
  await expect(page.locator('#world')).toHaveAttribute('data-renderer', 'webgl');
  await expect(page.locator('#world-location')).toHaveText('The Garden Gate');
  await expect(page.locator('#world')).toHaveAttribute('data-portal-count', '2');
  // The world map of the Adventure has 5 places.
  await expect(page.locator('#world')).toHaveAttribute('data-place-count', '5');
  // The "Change the world" panel stays under the 3D world.
  await expect(page.locator('#change-panel')).toBeVisible();
  await page.screenshot({ path: testInfo.outputPath('wish-3d-desktop.png') });
  // Waiting and moving do not advance the graph, roll dice, or change health.
  const stationary = await view(page);
  const sentBefore = sent.length;
  const positionBefore = Number(await page.locator('#world').getAttribute('data-player-z'));
  await page.locator('#world-canvas').focus();
  await page.keyboard.down('ArrowDown');
  await page.waitForTimeout(400);
  expect(Number(await page.locator('#world').getAttribute('data-player-z'))).toBeGreaterThan(positionBefore);
  await page.keyboard.up('ArrowDown');
  await page.waitForTimeout(400);
  expect((await view(page)).reports).toEqual(stationary.reports);
  expect((await view(page)).character.hp).toBe(stationary.character.hp);
  expect(sent).toHaveLength(sentBefore);
  // The server decides, even if a client sends an input that the game does not offer.
  const rejected = await page.request.post('/api/input', { data: { choose: { choice: 999999 } } });
  expect(rejected.status()).toBe(400);
  expect((await view(page)).reports).toEqual(stationary.reports);
  // A walk to a Choice sends exactly that input. The landscape is not built again.
  const builds = await page.locator('#world').getAttribute('data-world-builds');
  await walkThrough(page, 0);
  await expect(page.locator('#world')).toHaveAttribute('data-world-builds', builds);
  await expect(page.locator('#world-location')).toHaveText('The Green Dragon');
  await page.reload();
  await settled(page);
  await expect(page.locator('#world-location')).toHaveText('The Green Dragon');
  await walkThrough(page, 1);
  await expect(page.locator('#world-location')).toHaveText('Teeth in the Hedge');
  let current = await walkThrough(page, 0);
  expect(current.phase).toBe('fight');
  await expect(page.locator('[data-actor="Grey Wolf"]')).toHaveCount(1);
  await expect(page.locator('[data-object="shield"]')).toHaveCount(1);
  await page.screenshot({ path: testInfo.outputPath('combat-3d.png') });
  let turns = 0;
  while (current.phase === 'fight' && turns++ < 80) {
    await page.locator('#world-combat-actions button').first().click();
    await settled(page);
    current = await view(page);
  }
  // Finish the Adventure through the server, without a walk for each Scene.
  while (current.phase === 'scene' && turns++ < 200) {
    current = await (await page.request.post('/api/input', { data: { revision: current.worldRevision, input: current.scene.choices[0].input } })).json();
  }
  await page.reload();
  await settled(page);
  expect(['dead', 'ended']).toContain(current.phase);
  await expect(page.locator('#over')).toBeVisible();
  await expect(page.locator('#world')).toHaveAttribute('data-portal-count', '0');
  expect(errors).toEqual([]);
  await page.locator('#again').click();
  await settled(page);
  await expect(page.locator('#world-location')).toHaveText('The Garden Gate');
  // A phone screen keeps the move buttons and has no sideways scroll.
  await page.setViewportSize({ width: 390, height: 844 });
  await expect(page.locator('[data-move="arrowup"]')).toBeVisible();
  expect(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth)).toBe(true);
  await page.screenshot({ path: testInfo.outputPath('wish-3d-mobile.png') });
});
