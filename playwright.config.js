import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: './tests',
  testMatch: 'spatial.browser.spec.js',
  workers: 1,
  timeout: 240000,
  expect: { timeout: 15000 },
  use: {
    baseURL: 'http://127.0.0.1:8093',
    viewport: { width: 1360, height: 900 },
    screenshot: 'only-on-failure',
    trace: 'retain-on-failure',
    launchOptions: {
      executablePath: process.env.PLAYWRIGHT_CHROME_PATH || undefined,
      args: ['--enable-webgl', '--use-gl=angle', '--use-angle=swiftshader', '--enable-unsafe-swiftshader'],
    },
  },
  webServer: {
    command: 'RPG_FAKE_API=tests/fake-api .lake/build/bin/rpg --port 8093 --seed 7',
    url: 'http://127.0.0.1:8093/api/view',
    // Refuse an occupied port instead of running tests against the player's game.
    reuseExistingServer: false,
    timeout: 120000,
  },
});
