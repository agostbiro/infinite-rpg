// Verified RPG page.
// The page only draws what the server sends and sends back the Player's clicks.
// All rules and dice are in Lean. The page never makes up a die face: every face it
// shows comes from a Report. The 3D world (world3d.js) makes one object for each input that
// the server offers, and sends that input unchanged (docs/adr/0006-the-3d-world-shows-the-graph.md).
import { SpatialGame } from './world3d.js';
import { playbackView, reportDuration } from './playback.js';

(() => {
  const $ = (id) => document.getElementById(id);

  /** Make an element with a class and text. */
  function el(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  const S = {
    view: null,      // the last view from the server
    playbackBase: null, // the view before the last input, while its new Reports play
    shown: 0,        // how many Reports are on screen
    playing: false,  // true while new Reports play one at a time
    skip: false,     // true after a click on "Skip"
    wake: null,      // ends the current pause early
    busy: false,     // true while a request is out
    speed: 1,        // the speed of the dice: 1, 2, or 0 (no wait)
    wishOpen: false, // true while the Wish form is open on the front page
    gridKey: null,   // the cards on screen, as JSON, so a poll can tell if they changed
    starting: null,  // while a click starts an Adventure: { key, text }. `key` names what was clicked
    lost: false,     // true after a poll could not reach the server
  };

  /** The 3D world, or null if this browser cannot draw it (no WebGL 2). Then the page shows the
   * text controls only. */
  let spatial = null;

  // ---------- Server ----------

  /** The server sent a reply, so it can be reached. Clear the line that says it cannot. */
  function reached() {
    if (!S.lost) return;
    S.lost = false;
    if (S.view && S.view.phase === 'title') renderFrontStatus(S.view);
  }

  async function fetchView() {
    const r = await fetch('/api/view', { cache: 'no-store' });
    reached();
    return r.json();
  }

  /** An error with the server's own reason, for a reply that is not a view. */
  class ServerRefused extends Error {}

  /** The text for a toast after a failed request: the server's reason, if it gave one. */
  function failText(e) {
    return e instanceof ServerRefused ? e.message : 'Cannot reach the game server. Check that it still runs.';
  }

  /** A small turning ring that shows the page waits. Screen readers skip it: the text next to it
   * says what the page waits for. */
  function spinnerEl() {
    const s = el('span', 'spinner');
    s.setAttribute('aria-hidden', 'true');
    return s;
  }

  async function post(path, body) {
    const r = await fetch(path, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: body === undefined ? '' : JSON.stringify(body),
    });
    reached();
    const type = r.headers.get('Content-Type') || '';
    if (!type.startsWith('application/json')) {
      // A refusal such as 403, 404, or 413 comes as plain text, not as a view.
      const text = (await r.text()).trim();
      throw new ServerRefused('The server refused that (' + r.status + '): ' + (text || r.statusText));
    }
    return { ok: r.ok, status: r.status, view: await r.json() };
  }

  // ---------- Reports ----------

  /** The kind of a Report, such as "attack". Reports with no data are plain strings. */
  const kindOf = (r) => (typeof r === 'string' ? r : Object.keys(r)[0]);
  /** The data of a Report. */
  const dataOf = (r) => (typeof r === 'string' ? {} : r[kindOf(r)]);

  /** The dice in a Report, or null. `red` is true for damage dice. */
  function diceOf(r) {
    const k = kindOf(r);
    const d = dataOf(r);
    if (k === 'successRoll' || k === 'attack' || k === 'dodge') return { faces: d.roll.faces, red: false, rolled: true };
    if (k === 'damage' && d.faces.length > 0) return { faces: d.faces, red: true, rolled: !d.maxed };
    return null;
  }

  const MANEUVER = { attack: 'Attack', allOutAttack: 'All-Out Attack', allOutDefense: 'All-Out Defense' };

  const RESULT = {
    criticalSuccess: ['Critical success!', 'crit'],
    success: ['Success.', 'good'],
    failure: ['Failure.', 'bad'],
    criticalFailure: ['Critical failure!', 'bad'],
  };

  // Pip places on a 3 by 3 grid, for each face.
  const PIPS = { 1: [4], 2: [0, 8], 3: [0, 4, 8], 4: [0, 2, 6, 8], 5: [0, 2, 4, 6, 8], 6: [0, 2, 3, 5, 6, 8] };

  /** Draw dice with the given faces. */
  function diceEl(faces, red, maxed) {
    const box = el('span', 'dice');
    for (const f of faces) {
      const die = el('span', 'die' + (red ? ' red' : '') + (maxed ? ' max' : ''));
      die.setAttribute('role', 'img');
      die.setAttribute('aria-label', 'die showing ' + f);
      die.dataset.face = String(f);
      const on = PIPS[f] || [];
      for (let i = 0; i < 9; i++) die.appendChild(el('i', on.includes(i) ? 'on' : ''));
      box.appendChild(die);
    }
    return box;
  }

  /** Add the dice, the total, and the result of a roll to a line. */
  function addRoll(li, roll) {
    li.append(diceEl(roll.faces, false, false));
    li.append(el('span', 'after', '= ' + roll.total + '. '));
    const [text, cls] = RESULT[roll.result] || [roll.result, ''];
    li.append(el('span', 'result ' + cls, text));
  }

  /** One line of the story for a Report that is not a Scene. */
  function reportEl(r) {
    const k = kindOf(r);
    const d = dataOf(r);
    const li = el('li', k);
    switch (k) {
      case 'picked':
        li.textContent = 'You choose: ' + d.text;
        break;
      case 'successRoll':
        li.append(d.who + ' rolls ' + d.what + ', needing ' + d.roll.target + ' or less: ');
        addRoll(li, d.roll);
        li.classList.add(d.roll.result.endsWith('uccess') ? 'good' : 'bad');
        break;
      case 'cannotTry':
        li.textContent = d.level === null
          ? d.who + ' cannot use ' + d.what + ' untrained. Failure.'
          : d.who + ' cannot try ' + d.what + ': the effective skill ' + d.level + ' is below 3. Failure.';
        li.classList.add('bad');
        break;
      case 'fightStarts':
        li.textContent = 'A Fight starts: ' + d.hero.name + ' against ' + d.foes.map((f) => f.name).join(', ') + '.';
        break;
      case 'round':
        li.textContent = 'Round ' + d.n;
        break;
      case 'maneuver':
        li.textContent = d.who + ' chooses ' + (MANEUVER[d.m] || d.m) + '.';
        break;
      case 'attack':
        li.append(d.attackerName + ' attacks ' + d.defenderName + ' ' + d.withWeapon +
          ', needing ' + d.roll.target + ' or less: ');
        addRoll(li, d.roll);
        break;
      case 'cannotAttack':
        li.textContent = d.who + ' cannot attack: the effective skill ' + d.level + ' is below 3.';
        break;
      case 'noDefense':
        li.textContent = d.who + ' cannot Dodge after an All-Out Attack.';
        li.classList.add('bad');
        break;
      case 'dodge':
        li.append(d.who + ' tries to Dodge, needing ' + d.roll.target + ' or less: ');
        addRoll(li, d.roll);
        break;
      case 'damage': {
        li.classList.add('hit');
        li.append('Hit! Damage ');
        if (d.maxed) li.append('(a roll of 3: every die counts as 6) ');
        li.append(diceEl(d.faces, true, d.maxed));
        const add = d.add === 0 ? '' : (d.add > 0 ? '+ ' + d.add + ' ' : '- ' + (-d.add) + ' ');
        li.append(el('span', 'after', add + '= ' + d.basic + ' ' + d.kind + '. DR ' + d.dr + '. ' +
          d.defenderName + ' takes ' + d.injury + ' injury and has ' + d.hp + ' HP left.'));
        break;
      }
      case 'falls':
        li.textContent = d.name + ' falls.';
        li.classList.add('fall');
        break;
      case 'fightWon':
        li.textContent = 'You win the Fight.';
        li.classList.add('won');
        break;
      case 'died':
        li.textContent = d.who + ' dies. The Adventure is over.';
        li.classList.add('died');
        break;
      case 'worldRule':
        li.append(el('strong', '', d.name + ': '), document.createTextNode(d.text));
        break;
      default:
        li.textContent = k;
    }
    return li;
  }

  // ---------- Story ----------

  /** Draw the story from the first `n` Reports. */
  function renderStory(n) {
    const reports = S.view.reports;
    const chapters = [];
    for (let i = 0; i < n; i++) {
      if (kindOf(reports[i]) === 'scene') chapters.push({ scene: dataOf(reports[i]), items: [] });
      else if (chapters.length > 0) chapters[chapters.length - 1].items.push(reports[i]);
    }
    const scroll = $('scroll');
    scroll.textContent = '';
    if (S.view.intro) {
      const intro = el('section', 'chapter intro');
      if (S.view.world) intro.appendChild(el('p', 'intro-world', S.view.world));
      intro.appendChild(el('p', 'intro-text', S.view.intro));
      scroll.appendChild(intro);
    }
    chapters.forEach((ch, ci) => {
      const current = ci === chapters.length - 1;
      const sec = el('section', 'chapter ' + (current ? 'current' : 'past'));
      sec.appendChild(el('h2', '', ch.scene.title));
      sec.appendChild(el('p', 'scene-text', ch.scene.text));
      const log = el('ol', 'log');
      for (const r of ch.items) log.appendChild(reportEl(r));
      sec.appendChild(log);
      scroll.appendChild(sec);
    });
  }

  /** Add Report `i` to the story. With `animate`, its dice tumble for about a second. */
  function appendReport(i, animate) {
    const r = S.view.reports[i];
    if (kindOf(r) === 'scene') {
      renderStory(i + 1);
      return;
    }
    const logs = document.querySelectorAll('#scroll .chapter.current .log');
    const log = logs[logs.length - 1];
    if (!log) return;
    for (const f of log.querySelectorAll('.featured')) f.classList.remove('featured');
    const li = reportEl(r);
    const dice = diceOf(r);
    if (animate && dice) {
      li.classList.add('featured');
      if (dice.rolled) {
        li.classList.add('pending');
        for (const die of li.querySelectorAll('.die')) die.classList.add('tumble');
        setTimeout(() => li.classList.remove('pending'), 1000);
      }
    }
    log.appendChild(li);
  }

  // ---------- Fight state, read from the Reports ----------

  /** The Character's HP after the first `n` Reports, from the last hit on the Character, or null
   * if no hit on the Character is shown yet. */
  function heroHPAt(n) {
    let hp = null;
    for (let i = 0; i < n; i++) {
      const r = S.view.reports[i];
      if (kindOf(r) === 'damage' && dataOf(r).defender === null) hp = dataOf(r).hp;
    }
    return hp;
  }

  /** Set an HP bar to `hp` out of `max`. */
  function setBar(bar, hp, max) {
    const pct = Math.max(0, Math.min(100, (100 * hp) / Math.max(1, max)));
    bar.firstChild.style.width = pct + '%';
    bar.classList.toggle('low', hp > 0 && 3 * hp < max);
    bar.classList.toggle('out', hp <= 0);
  }

  function hpBar() {
    const b = el('div', 'hpbar');
    b.appendChild(el('i'));
    return b;
  }

  // ---------- The text controls: Choices, Maneuvers, and the end ----------

  /** One button for each input that the view offers, in the order the server sends them. Each
   * button sends its input unchanged. The 3D world makes the same list (`portalsForView`). */
  function inputButtons(v) {
    if (v.phase === 'scene' && v.scene) {
      return v.scene.choices.filter((ch) => ch.input !== null).map((ch) => {
        const b = el('button', 'choice', ch.text);
        b.type = 'button';
        b.onclick = () => send(ch.input);
        return b;
      });
    }
    if (v.phase === 'fight' && v.fight) {
      return v.fight.maneuvers.flatMap((m) => m.options.map((opt) => {
        const b = el('button', 'maneuver');
        b.type = 'button';
        const target = m.attacks && opt.target !== null ? ' · ' + (v.fight.foes[opt.target]?.name || 'Target') : '';
        b.append(el('b', '', m.label + target), el('span', '', m.help));
        (m.effects || []).forEach((effect) => b.append(el('small', 'tactic-effect', effect)));
        b.onclick = () => send(opt.input);
        return b;
      }));
    }
    return [];
  }

  /** The Fight as text: the round, and the HP of each being. */
  function renderFight(v) {
    const box = $('fight');
    box.hidden = !(v.phase === 'fight' && v.fight);
    if (box.hidden) return;
    $('round').textContent = 'Round ' + v.fight.round;
    const list = $('fighters');
    list.textContent = '';
    for (const f of [v.fight.hero, ...v.fight.foes]) {
      const li = el('li', f.alive === false || f.hp <= 0 ? 'down' : '');
      li.append(el('b', '', f.name), ' ' + f.weapon + ', ' + f.damage + ', DR ' + f.dr + '. HP ' + f.hp + ' / ' + f.maxHP + '.');
      list.appendChild(li);
    }
  }

  /** `true` while the page must not send an input: Reports play, a request is out, or the
   * Dungeon Master works on a change. */
  function inputLocked() {
    return S.playing || S.busy || S.view.generation.state === 'running';
  }

  /** Draw the input buttons, the Fight text, or the end of the Adventure. */
  function renderMat() {
    const v = S.view;
    const choices = $('choices');
    choices.textContent = '';
    $('over').hidden = true;
    $('skip').hidden = !S.playing;
    $('leave').disabled = inputLocked();
    renderFight(v);
    $('fight-hint').textContent = v.phase === 'fight' && !inputLocked() ? 'Your turn. Choose a Maneuver.' : '';
    markState();
    syncSpatial();
    if (inputLocked()) return;
    for (const b of inputButtons(v)) choices.appendChild(b);
    if (gameOver(v)) {
      const over = $('over');
      over.hidden = false;
      over.classList.toggle('dead', v.phase === 'dead');
      if (v.phase === 'dead') {
        $('over-title').textContent = 'The Adventure is over';
        $('over-text').textContent = v.character.name + ' died in the Fight. This is not an Ending.';
      } else {
        $('over-title').textContent = 'The End';
        $('over-text').textContent = 'You reached an Ending: ' + (v.scene ? v.scene.title.replace(/^Ending:\s*/, '') : '') + '.';
      }
      // A live change is not saved: "Play again" and leaving start the original Adventure.
      if ((v.worldRules || []).length > 0) {
        $('over-text').textContent += ' Play again and ← Adventures start the original Adventure, without your rule changes.';
      }
    }
  }

  // ---------- The 3D world ----------

  /** Give the 3D world the view to show. While Reports play, it shows the state at the last Report
   * on screen, not the final reply. It can send an input only when the page waits for the Player. */
  function syncSpatial() {
    if (!spatial || !S.view) return;
    try {
      const shown = S.playing ? playbackView(S.playbackBase, S.view, S.shown) : S.view;
      spatial.update(shown, !inputLocked());
    } catch (error) {
      spatial.ready = false;
      document.body.classList.add('journal-open');
      toast('The 3D view could not show every choice. Use the journal: ' + error.message);
    }
  }

  /** Show a Report with dice or a result over the 3D world, with the same text as the journal. */
  function showSpatialReport(r) {
    const tray = $('world-events');
    const k = kindOf(r);
    // A new Choice clears the old result. A new Scene keeps it: the 3D view hides it at Continue.
    if (k === 'picked') { tray.hidden = true; return; }
    if (['scene', 'round', 'maneuver'].includes(k)) return;
    tray.hidden = false;
    const row = reportEl(r);
    row.classList.add('world-event');
    if (S.speed !== 0) for (const die of row.querySelectorAll('.die')) die.classList.add('tumble');
    $('world-event-list').replaceChildren(row);
    tray.dataset.report = k;
    spatial.presentReport(r);
  }

  // ---------- Character panel ----------

  function renderCharacter() {
    const c = S.view.character;
    const heroHP = heroHPAt(S.shown);
    const hp = heroHP === null ? c.maxHP : heroHP;
    const p = $('character');
    p.textContent = '';
    p.appendChild(el('h2', '', 'Character'));
    p.appendChild(el('p', 'char-name', c.name));
    p.appendChild(el('p', 'char-sub', 'The Character you play'));
    if (S.view.background) p.appendChild(el('p', 'char-bg', S.view.background));
    const attrs = el('div', 'attrs');
    for (const [k, label] of [['st', 'ST'], ['dx', 'DX'], ['iq', 'IQ'], ['ht', 'HT']]) {
      const a = el('div', 'attr');
      a.append(el('b', '', String(c[k])), el('span', '', label));
      attrs.appendChild(a);
    }
    p.appendChild(attrs);
    const row = el('div', 'hp-row');
    row.append(el('span', '', 'Hit Points (HP)'), el('b', '', hp + ' / ' + c.maxHP));
    p.appendChild(row);
    const bar = hpBar();
    p.appendChild(bar);
    setBar(bar, hp, c.maxHP);
    const stats = el('ul', 'stat-list');
    const stat = (k, v) => { const li = el('li'); li.append(el('span', '', k), el('b', '', String(v))); stats.appendChild(li); };
    stat('Basic Speed', c.speed);
    stat('Dodge', c.dodge);
    stat('Attack', c.attack);
    p.appendChild(stats);
    p.appendChild(el('p', 'sub-h', 'Skills'));
    const skills = el('ul', 'stat-list');
    for (const s of c.skills) {
      const li = el('li');
      li.append(el('span', '', s.name), el('b', '', String(s.level)));
      skills.appendChild(li);
    }
    p.appendChild(skills);
    p.appendChild(el('p', 'sub-h', 'Gear'));
    const gear = el('ul', 'stat-list');
    const g1 = el('li'); g1.append(el('span', '', c.weapon), el('b', '', c.damage)); gear.appendChild(g1);
    const g2 = el('li'); g2.append(el('span', '', c.armor), el('b', '', 'DR ' + c.dr)); gear.appendChild(g2);
    p.appendChild(gear);
  }

  // ---------- Whole page ----------

  /** The "New Adventure" tile: a button, or the Wish form, or the steps of the work on a Wish. */
  function renderWish(v) {
    const gen = v.generation;
    const running = gen.state === 'running';
    const showSteps = gen.state !== 'idle';
    const open = showSteps || (S.wishOpen && gen.available);
    $('new-tile').classList.toggle('open', open);
    $('new-open').hidden = open;
    $('new-open').disabled = !gen.available || S.starting !== null;
    $('new-sub').textContent = gen.available
      ? 'Tell an AI Dungeon Master what you want to play'
      : 'Not available: the Dungeon Master is not connected. Set ANTHROPIC_API_KEY, then run the game again.';
    $('wish-panel').hidden = !open;
    $('wish-form').hidden = showSteps;
    $('progress').hidden = !showSteps;
    $('cancel').hidden = !running;
    $('retry').hidden = gen.state !== 'failed';
    $('dismiss').hidden = gen.state !== 'refused' && gen.state !== 'failed';
    const ready = gen.state === 'ready';
    $('ready').hidden = !ready;
    $('play-now').hidden = !ready;
    $('later').hidden = !ready;
    // While a click starts an Adventure, no other button may send a request. The button that was
    // clicked is only marked disabled (`aria-disabled`), so it keeps the keyboard focus. Its click
    // does nothing while the page waits (`startGame` returns at once).
    const starting = S.starting !== null;
    const playNowClicked = starting && S.starting.key === 'play-now';
    $('play-now').disabled = starting && !playNowClicked;
    $('play-now').setAttribute('aria-disabled', String(playNowClicked));
    $('play-now').setAttribute('aria-busy', String(playNowClicked));
    for (const id of ['later', 'retry', 'dismiss', 'wish-send']) $(id).disabled = starting;
    if (ready) $('ready-title').textContent = v.adventure;
    $('progress-wish').textContent = gen.wish ? 'Your Wish: ' + gen.wish : '';
    const list = $('progress-steps');
    list.textContent = '';
    gen.steps.forEach((st, i) => {
      const li = el('li', '', st.text);
      const last = i === gen.steps.length - 1;
      if (st.errors.length > 0) {
        li.classList.add('bad');
        const ul = el('ul');
        for (const e of st.errors) ul.appendChild(el('li', '', e));
        li.appendChild(ul);
      } else if (st.text.startsWith('The Adventure passed')) {
        li.classList.add('good');
      } else if (last && running) {
        li.classList.add('now');
        li.prepend(spinnerEl());
      } else if (last) {
        li.classList.add('bad');
      }
      list.appendChild(li);
    });
    // Until the first poll brings the first step, say that the Wish is on its way.
    if (running && gen.steps.length === 0) {
      const li = el('li', 'now', 'Sending your Wish to the Dungeon Master...');
      li.prepend(spinnerEl());
      list.appendChild(li);
    }
  }

  /** A line at the foot of a card that says the server works on it. */
  function busyLine(text) {
    const line = el('span', 'card-busy');
    line.append(spinnerEl(), el('span', '', text));
    return line;
  }

  /** One Adventure card. Options: `onPlay` makes a click start play; `why` greys the card and
   * says why it cannot be played; `onRecheck` adds a "Check again" button to such a card;
   * `checking` says the server still checks it, so it cannot be clicked yet; `starting` is the
   * text while the page waits for the click to start play. */
  function adventureCard(c, key, o) {
    const button = !!o.onPlay || !!o.checking;
    const cls = 'tile adv-card' + (o.why !== undefined ? ' failed' : '') +
      (o.checking ? ' checking' : '') + (o.starting ? ' starting' : '');
    const card = el(button ? 'button' : 'div', cls);
    card.dataset.card = key;
    if (button) {
      card.type = 'button';
      // The card that was clicked is only marked disabled, so it keeps the keyboard focus. Its
      // click does nothing while the page waits (`startGame` returns at once).
      card.disabled = !!o.checking || (!!o.disabled && !o.starting);
      if (o.starting) card.setAttribute('aria-disabled', 'true');
      if (o.onPlay) card.onclick = o.onPlay;
    }
    if (o.checking || o.starting) card.setAttribute('aria-busy', 'true');
    card.append(el('span', 'card-title', c.title));
    if (c.world) card.append(el('span', 'card-world', c.world));
    if (c.hero) card.append(el('span', 'card-hero', 'You play ' + c.hero));
    if (c.about) card.append(el('span', 'card-about', c.about));
    if (o.why !== undefined) {
      card.append(el('span', 'card-why', 'Fails the checker now, so you cannot play it: ' + o.why));
      if (o.onRecheck) card.append(recheckButton(key, o));
    } else if (o.starting) {
      card.append(busyLine(o.starting));
    } else if (o.checking) {
      card.append(busyLine('Checking it against the rules...'));
    } else {
      card.append(el('span', 'card-source', c.source));
    }
    return card;
  }

  /** The "Check again" button of a card that fails. It sends a load, which checks the save again:
   * if it passes now, play starts; if not, the card shows the new reason. Like a clicked card, the
   * clicked button is only marked disabled while the page waits, so it keeps the keyboard focus. */
  function recheckButton(key, o) {
    const b = el('button', 'small-button recheck');
    b.type = 'button';
    b.dataset.card = 'recheck:' + key;
    b.disabled = !!o.disabled && !o.starting;
    if (o.starting) {
      b.setAttribute('aria-disabled', 'true');
      b.setAttribute('aria-busy', 'true');
      b.append(spinnerEl(), ' ' + o.starting);
    } else {
      b.textContent = 'Check again';
    }
    b.onclick = o.onRecheck;
    return b;
  }

  /** The text of the status line while a load checks a saved Adventure again. */
  const checkText = (title) => 'Checking ' + title + ' against the rules and the balance check...';

  /** The grid: the "New Adventure" tile, the saved Adventures (newest first), and the built-in one.
   * Each saved Adventure keeps its place when its check ends, so the cards do not move under the
   * pointer. One that the server still checks cannot be clicked yet; one that fails is greyed. */
  function renderGrid(v) {
    const grid = $('grid');
    const busy = v.generation.state === 'running' || S.starting !== null;
    const startKey = S.starting ? S.starting.key : null;
    // A poll every 2 seconds must not rebuild the same cards: that would take away keyboard focus
    // and lose a click. So draw again only when the cards change.
    const key = JSON.stringify([v.saved, v.builtin, busy, startKey]);
    if (key === S.gridKey && grid.querySelector('.adv-card')) return;
    S.gridKey = key;
    // A card that a check finished on is drawn again. Keep the keyboard focus on the same card.
    const active = document.activeElement;
    const focused = active && active.dataset && active.dataset.card ? active.dataset.card : null;
    for (const old of grid.querySelectorAll('.adv-card')) old.remove();
    for (const a of v.saved) {
      // A save that passed starts at once (the server trusts its verdict); any other is checked.
      const start = { key: a.id, text: a.ok ? 'Starting ' + a.title + '...' : checkText(a.title) };
      if (!a.ok && !a.checking) {
        grid.appendChild(adventureCard(a, a.id, {
          why: a.why || 'it does not read',
          onRecheck: () => startGame('/api/load', { id: a.id }, start),
          disabled: busy,
          starting: startKey === a.id ? 'Checking again...' : undefined,
        }));
        continue;
      }
      grid.appendChild(adventureCard(a, a.id, {
        onPlay: () => startGame('/api/load', { id: a.id }, start),
        disabled: busy,
        checking: a.checking,
        starting: startKey === a.id ? 'Checking it again before you play...' : undefined,
      }));
    }
    // The built-in Adventure comes after the saved ones. It needs no API key, and the server
    // checked it when it started, so it starts at once.
    if (v.builtin) {
      const builtinStart = { key: 'builtin', text: 'Starting ' + v.builtin.title + '...' };
      grid.appendChild(adventureCard(v.builtin, 'builtin', {
        onPlay: () => startGame('/api/builtin', undefined, builtinStart),
        disabled: busy,
        starting: startKey === 'builtin' ? 'Starting...' : undefined,
      }));
    }
    if (focused !== null) {
      const again = Array.from(grid.querySelectorAll('button[data-card]')).find((c) => c.dataset.card === focused);
      if (again && !again.disabled) again.focus();
    }
  }

  /** What the Front Page waits for now, as one line, or null. */
  function frontStatus(v) {
    if (S.starting) return { text: S.starting.text, busy: true };
    if (S.lost) return { text: 'Cannot reach the game server. Check that it still runs.', bad: true };
    const checking = v.saved.filter((a) => a.checking).length;
    if (checking === 0) return null;
    const done = v.saved.length - checking;
    return {
      text: 'Checking the saved Adventures again: ' + done + ' of ' + v.saved.length + ' done.',
      busy: true,
    };
  }

  /** Show the status line of the Front Page. It keeps its height when it is empty, so the cards
   * do not move under the pointer. It changes only when its text changes, so a screen reader does
   * not read the same line again on each poll. */
  function renderFrontStatus(v) {
    const box = $('front-status');
    const st = frontStatus(v);
    const text = st ? st.text : '';
    if (box.dataset.text === text) return;
    box.dataset.text = text;
    box.classList.toggle('bad', !!(st && st.bad));
    box.textContent = '';
    if (st && st.busy) box.append(spinnerEl());
    box.append(text);
  }

  function renderTitle() {
    const v = S.view;
    $('busy-note').hidden = v.generation.state !== 'running';
    renderWish(v);
    renderGrid(v);
    renderFrontStatus(v);
  }

  /** Tell tests and screen readers whether the page waits for the Player. */
  function markState() {
    const ready = !S.playing && !S.busy && S.view?.generation.state !== 'running';
    document.body.dataset.state = ready ? 'ready' : 'busy';
    document.body.dataset.shown = String(S.shown);
    $('change-send').disabled = !ready || !S.view?.canChange;
  }

  /** Describe the actual numeric effect alongside the Dungeon Master's fiction. */
  function ruleEffect(rule) {
    const triggers = {
      always: 'always', wounded: 'at half HP or less', desperate: 'at one third HP or less',
      reckless: 'while using All-Out Attack', guarding: 'while using All-Out Defense',
      againstReckless: 'against All-Out Attack', againstGuarding: 'against All-Out Defense',
      againstFlame: 'against a flamethrower'
    };
    const signed = (n) => n > 0 ? '+' + n : String(n);
    const effects = [];
    if (rule.hitBonus) effects.push(signed(rule.hitBonus) + ' to hit');
    if (rule.damageBonus) effects.push(signed(rule.damageBonus) + ' damage');
    if (rule.armorBonus) effects.push('+' + rule.armorBonus + ' armor');
    return (rule.side === 'hero' ? 'You' : 'Enemies') + ', ' + triggers[rule.trigger] + ': ' + effects.join(', ') + '.';
  }

  /** The game stays paused while a proposed rule change is being checked. */
  function renderChange() {
    const v = S.view;
    const gen = v.generation;
    const changing = gen.mode === 'change' && gen.state !== 'idle';
    const running = changing && gen.state === 'running';
    $('change-panel').hidden = !v.canChange && !(v.worldRules || []).length && !changing;
    $('change-off').hidden = gen.available;
    $('change-form').hidden = !v.canChange || !gen.available || changing;
    $('change-send').disabled = S.busy || S.playing || gen.state === 'running';
    $('change-progress').hidden = !changing;
    $('change-status').textContent = running ? 'Your game is paused. The Dungeon Master is working on: ' + gen.wish : 'Your game is unchanged.';
    $('change-cancel').hidden = !running;
    $('change-retry').hidden = !changing || running;
    $('change-dismiss').hidden = !changing || running;
    const steps = $('change-steps');
    steps.textContent = '';
    for (const step of gen.steps.slice(-4)) {
      const item = el('li', '', step.text);
      if (step.errors.length) {
        const detail = el('details');
        detail.append(el('summary', '', 'What needs adjusting'));
        const errors = el('ul');
        step.errors.forEach((error) => errors.append(el('li', '', error)));
        detail.append(errors);
        item.append(detail);
      }
      steps.append(item);
    }
    const rules = $('active-rules');
    rules.textContent = '';
    if ((v.worldRules || []).length) rules.append(el('h3', '', 'Rules of this world'));
    for (const rule of v.worldRules || []) {
      const entry = el('p');
      entry.append(el('strong', '', rule.name + '. '), document.createTextNode(rule.description));
      entry.append(el('br'), el('small', '', ruleEffect(rule)));
      rules.append(entry);
    }
  }

  function renderAll() {
    const v = S.view;
    $('loading').hidden = true;
    $('seed').textContent = 'seed ' + v.seed;
    const title = v.phase === 'title';
    $('title-screen').hidden = !title;
    $('table').hidden = title;
    // The seed belongs to a game, so the front page does not show it.
    $('seed').hidden = title;
    document.title = (title ? 'Choose an Adventure' : v.adventure) + ' · Verified RPG';
    // Without WebGL the world box holds only the end panel and the notice; it follows the table.
    if (!spatial) $('world').hidden = title;
    if (title) {
      syncSpatial();
      renderTitle();
      markState();
      return;
    }
    $('adventure-title').textContent = v.adventure;
    renderStory(S.shown);
    renderMat();
    renderCharacter();
    renderChange();
  }

  function scrollToMat() {
    if (spatial) return;
    $('mat').scrollIntoView({ block: 'end', behavior: 'smooth' });
  }

  /** Wait `ms` milliseconds, or less after a click on "Skip". */
  function pause(ms) {
    return new Promise((resolve) => {
      if (S.skip) { resolve(); return; }
      const t = setTimeout(resolve, ms);
      S.wake = () => { clearTimeout(t); resolve(); };
    });
  }

  /** Play the new Reports one at a time, then show the buttons. */
  async function play() {
    S.playing = true;
    S.skip = false;
    renderAll();
    const reports = S.view.reports;
    while (S.shown < reports.length && !S.skip) {
      const i = S.shown;
      const r = reports[i];
      S.shown = i + 1;
      appendReport(i, S.speed !== 0);
      renderMat();
      renderCharacter();
      if (spatial) showSpatialReport(r);
      scrollToMat();
      await pause(reportDuration(r, S.speed, !!spatial));
    }
    S.shown = reports.length;
    S.playing = false;
    S.skip = false;
    S.wake = null;
    S.playbackBase = null;
    renderAll();
    scrollToMat();
  }

  let toastTimer = null;
  function toast(text) {
    const t = $('toast');
    t.textContent = text;
    t.hidden = false;
    clearTimeout(toastTimer);
    // A long reason, such as the errors of a check, stays longer, so the Player can read it.
    toastTimer = setTimeout(() => { t.hidden = true; }, Math.min(12000, Math.max(4000, 60 * text.length)));
  }

  /** Send one input, exactly as the server offered it. */
  async function send(input) {
    if (S.busy || S.playing) return;
    S.busy = true;
    if (S.view && S.view.phase !== 'title') renderMat();
    try {
      const { ok, view } = await post('/api/input', input);
      S.playbackBase = S.view;
      S.view = view;
      if (S.shown > view.reports.length) S.shown = view.reports.length;
      if (!ok) {
        toast(view.error || 'The game refused that input.');
        renderAll();
        return;
      }
      await play();
    } catch (e) {
      toast(failText(e));
    } finally {
      S.busy = false;
      if (S.view && S.view.phase !== 'title') renderMat();
      markState();
      schedulePoll();
    }
  }

  /** Start a new game with a new seed, and begin it. */
  async function playAgain() {
    if (S.busy || S.playing) return;
    S.busy = true;
    try {
      const fresh = await post('/api/new');
      S.view = fresh.view;
      S.shown = 0;
      S.busy = false;
      if (fresh.view.inputs.length > 0) await send(fresh.view.inputs[0]);
    } catch (e) {
      toast(failText(e));
    } finally {
      S.busy = false;
    }
  }

  /** Send a POST that loads an Adventure, such as a click on its card, then begin it.
   * `start` says what to show while the page waits: `{ key, text }`, where `key` is the id of the
   * card, "builtin", or "play-now". A load checks the saved
   * Adventure again, which takes a second or two. Until the reply comes, every card and button
   * that sends a request is disabled. */
  async function startGame(path, body, start) {
    if (S.busy || S.playing) return;
    S.busy = true;
    S.starting = start || null;
    if (S.view && S.view.phase === 'title') renderTitle();
    markState();
    try {
      const { ok, view } = await post(path, body);
      S.starting = null;
      S.view = view;
      S.shown = view.reports.length;
      S.wishOpen = false;
      if (!ok || view.phase !== 'title' || view.inputs.length === 0) {
        if (!ok) toast(view.error || 'The game refused that.');
        renderAll();
        // A refused card is drawn again as a grey card, so the focused element can be gone.
        keepFocus();
        return;
      }
      S.busy = false;
      await send(view.inputs[0]);
    } catch (e) {
      toast(failText(e));
    } finally {
      S.busy = false;
      if (S.starting !== null) {
        // The request failed with no reply: enable the cards and buttons again.
        S.starting = null;
        if (S.view && S.view.phase === 'title') renderTitle();
        keepFocus();
      }
      markState();
      schedulePoll();
    }
  }

  /** `true` if the game in play is over: an Ending, or the Character died. */
  function gameOver(v) {
    return v.phase === 'ended' || v.phase === 'dead' || (v.phase !== 'title' && v.inputs.length === 0);
  }

  /** Go back to the front page. A game that is not over asks first, because it is lost. */
  function leave() {
    if (S.busy || S.playing || !S.view) return;
    if (gameOver(S.view)) { action('/api/new').then(focusFront); return; }
    $('leave-dialog').showModal();
  }

  /** Load the game from the server and show it all at once. Until the view comes, the page says
   * that it loads. If the server cannot be reached, it says so and offers "Try again". */
  async function load() {
    $('loading').hidden = false;
    $('loading-spinner').hidden = false;
    $('loading-text').textContent = 'Loading the game...';
    $('loading-retry').hidden = true;
    try {
      const v = await fetchView();
      S.view = v;
      S.shown = v.reports.length;
      renderAll();
      schedulePoll();
    } catch (e) {
      $('loading-spinner').hidden = true;
      $('loading-text').textContent = failText(e) + ' Then click Try again.';
      $('loading-retry').hidden = false;
    }
  }

  /** Send a POST that changes the server state: a Wish, Later, a live change, or Cancel. */
  async function action(path, body) {
    if (S.busy || S.playing) return;
    S.busy = true;
    try {
      const { ok, view } = await post(path, body);
      S.view = view;
      S.shown = view.reports.length;
      if (!ok) toast(view.error || 'The game refused that.');
      renderAll();
    } catch (e) {
      toast(failText(e));
    } finally {
      S.busy = false;
      renderAll();
      schedulePoll();
    }
  }

  /** `true` while the server works in the background: the DM writes, or the server checks the
   * saved Adventures on the Front Page. */
  function serverWorking(v) {
    return !!v && (v.generation.state === 'running' ||
      (v.phase === 'title' && v.saved.some((a) => a.checking)));
  }

  let pollTimer = null;
  /** Ask the server for news every 2 seconds while it works in the background.
   * The state lives on the server, so a reload shows the same steps. */
  function schedulePoll() {
    clearTimeout(pollTimer);
    if (!serverWorking(S.view)) return;
    pollTimer = setTimeout(poll, 2000);
  }

  async function poll() {
    if (S.busy || S.playing) { schedulePoll(); return; }
    try {
      const v = await fetchView();
      if (S.busy || S.playing) { schedulePoll(); return; }
      const sameGame = S.view && v.seed === S.view.seed &&
        v.reports.length === S.view.reports.length && v.phase === S.view.phase;
      // Draw everything again only when it changed: during a live change, the steps change.
      const genChanged = JSON.stringify(v.generation) !== JSON.stringify(S.view.generation);
      if (v.phase === 'title' || !sameGame || genChanged) {
        S.view = v;
        S.shown = v.reports.length;
        renderAll();
      }
    } catch (e) {
      // Say it once: in the status line on the Front Page, else in a toast. The poll goes on,
      // and the next reply clears the line.
      if (!S.lost) {
        S.lost = true;
        if (S.view && S.view.phase === 'title') renderFrontStatus(S.view);
        else toast(failText(e));
      }
    }
    schedulePoll();
  }

  $('wish').addEventListener('input', () => {
    $('wish-count').textContent = $('wish').value.length + ' / 500';
  });
  $('wish-send').addEventListener('click', () => {
    const box = $('wish');
    // An empty box sends the example Wish shown as the placeholder. It goes into the box as real
    // text first, so the Player sees the Wish that was sent.
    if (!box.value.trim()) {
      box.value = box.placeholder;
      $('wish-count').textContent = box.value.length + ' / 500';
    }
    const wish = box.value.trim();
    if (!wish) { toast('Type a Wish first.'); return; }
    action('/api/wish', { wish, name: $('wish-name').value.trim(), gender: $('wish-gender').value });
  });
  $('cancel').addEventListener('click', async () => {
    try {
      const { view } = await post('/api/cancel');
      S.view = view;
      renderAll();
      focusFront();
      toast('The Dungeon Master stopped.');
    } catch (e) {
      toast(failText(e));
    }
  });
  $('retry').addEventListener('click', () => action('/api/retry'));
  /** Put keyboard focus on the front page: the Wish box if the form is open, else the
   * "New Adventure" button, else the first card. */
  function focusFront() {
    const open = $('new-open');
    let target = null;
    if (!$('wish-panel').hidden && !$('wish-form').hidden) target = $('wish');
    else if (!open.hidden && !open.disabled) target = open;
    else target = document.querySelector('button.adv-card:not(:disabled)');
    if (target) target.focus();
  }

  /** On the Front Page, keep the keyboard focus where it is if it is still on a control that can
   * be used. Else put it on the Front Page (`focusFront`). */
  function keepFocus() {
    if (!S.view || S.view.phase !== 'title') return;
    const a = document.activeElement;
    const usable = a && a !== document.body && a.isConnected && !a.disabled &&
      a.getAttribute('aria-disabled') !== 'true' && a.offsetParent !== null;
    if (!usable) focusFront();
  }

  $('dismiss').addEventListener('click', async () => { await action('/api/dismiss'); focusFront(); });
  // Load the Adventure that passed by its folder name, not whatever is loaded now: another tab
  // may have loaded another Adventure since.
  /** Empty the Wish form, after a Wish became an Adventure. */
  function clearWish() {
    $('wish').value = '';
    $('wish-name').value = '';
    $('wish-gender').value = 'dm';
    $('wish-count').textContent = '0 / 500';
  }

  $('play-now').addEventListener('click', () => {
    const id = S.view && S.view.generation.readyId;
    if (!id) return;
    clearWish();
    startGame('/api/load', { id }, { key: 'play-now', text: checkText(S.view.adventure) });
  });
  $('change-send').addEventListener('click', () => {
    const wish = $('change-request').value.trim();
    if (!wish) { toast('Describe the change you want first.'); return; }
    action('/api/change', { wish });
  });
  $('change-cancel').addEventListener('click', () => action('/api/cancel'));
  $('change-retry').addEventListener('click', () => action('/api/retry'));
  $('change-dismiss').addEventListener('click', () => action('/api/dismiss'));
  $('later').addEventListener('click', async () => {
    clearWish();
    S.wishOpen = false;
    await action('/api/dismiss');
    focusFront();
  });
  $('new-open').addEventListener('click', () => {
    S.wishOpen = true;
    renderAll();
    $('wish').focus();
  });
  $('wish-close').addEventListener('click', () => {
    S.wishOpen = false;
    renderAll();
    focusFront();
  });
  $('to-title').addEventListener('click', async () => { await action('/api/new'); focusFront(); });
  $('leave').addEventListener('click', leave);
  $('leave-yes').addEventListener('click', async () => {
    $('leave-dialog').close();
    await action('/api/new');
    focusFront();
  });
  $('leave-no').addEventListener('click', () => $('leave-dialog').close());
  $('again').addEventListener('click', playAgain);
  $('skip').addEventListener('click', () => {
    S.skip = true;
    if (S.wake) S.wake();
  });
  // The dice speed changes only how long a Report stays on screen, never what it says.
  $('world-speed').addEventListener('click', () => {
    S.speed = S.speed === 1 ? 2 : S.speed === 2 ? 0 : 1;
    $('world-speed').textContent = S.speed === 0 ? 'Dice: no wait' : 'Dice ×' + S.speed;
    if (S.speed === 0 && S.wake) S.wake();
  });
  // Another tab can move the game on. Catch up when this tab comes back.
  window.addEventListener('focus', async () => {
    if (S.busy || S.playing || !S.view) return;
    try {
      const v = await fetchView();
      // Another tab may have sent a Wish, or started or stopped a live change. On the Front Page,
      // a saved Adventure may also have changed, so the server checks it again.
      const wishChanged = JSON.stringify(v.generation) !== JSON.stringify(S.view.generation) ||
        (v.phase === 'title' && JSON.stringify(v.saved) !== JSON.stringify(S.view.saved));
      if (v.seed !== S.view.seed || v.reports.length !== S.view.reports.length || v.phase !== S.view.phase ||
          wishChanged) {
        S.view = v;
        S.shown = v.reports.length;
        renderAll();
        schedulePoll();
      }
    } catch (e) { /* The server is gone; the next click says so. */ }
  });

  $('loading-retry').addEventListener('click', load);

  try {
    spatial = new SpatialGame(send);
  } catch (error) {
    // No WebGL 2: the page shows the text controls, and says why.
    const notice = el('p', 'world-failed', 'This browser cannot show the 3D world, so the page shows the text version. To explore in 3D, turn on WebGL 2.');
    notice.setAttribute('role', 'status');
    $('world').appendChild(notice);
    $('world').dataset.renderer = 'unavailable';
  }
  load();
})();
