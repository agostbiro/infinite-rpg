// Verified RPG page.
// The page only draws what the server sends and sends back the Player's clicks.
// All rules and dice are in Lean. The page never makes up a die face: every face it
// shows comes from a Report.
'use strict';

(() => {
  const $ = (id) => document.getElementById(id);

  /** Make an element with a class and text. */
  function el(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  const SVG = 'http://www.w3.org/2000/svg';

  /** Make an SVG element with attributes. */
  function svgEl(tag, attrs) {
    const e = document.createElementNS(SVG, tag);
    for (const [k, v] of Object.entries(attrs || {})) e.setAttribute(k, String(v));
    return e;
  }

  const S = {
    view: null,      // the last view from the server
    mapView: null,   // the view whose map is on screen (it waits for the playback to end)
    shown: 0,        // how many Reports are on screen
    playing: false,  // true while new Reports play one at a time
    skip: false,     // true after a click on "Skip"
    wake: null,      // ends the current pause early
    busy: false,     // true while a request is out
    aim: null,       // the number of the Maneuver that waits for a target
    cardsFor: -1,    // the Report number of the Fight whose cards are on screen
    wishOpen: false, // true while the Wish form is open on the front page
    gridKey: null,   // the cards on screen, as JSON, so a poll can tell if they changed
  };

  // ---------- Server ----------

  async function fetchView() {
    const r = await fetch('/api/view', { cache: 'no-store' });
    return r.json();
  }

  /** An error with the server's own reason, for a reply that is not a view. */
  class ServerRefused extends Error {}

  /** The text for a toast after a failed request: the server's reason, if it gave one. */
  function failText(e) {
    return e instanceof ServerRefused ? e.message : 'Cannot reach the game server.';
  }

  async function post(path, body) {
    const r = await fetch(path, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: body === undefined ? '' : JSON.stringify(body),
    });
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

  const PICTURE_NAME = /^[a-z0-9-]+$/;
  const PICTURE_BASE = /^\/(pictures|saved\/[A-Za-z0-9_-][A-Za-z0-9._-]*)\/$/;

  /** The address of a Scene's Picture, or null if there is none to show yet.
   * For the built-in Adventure every Picture is ready. For a live one, only the Pictures
   * that passed the check on the server. */
  function pictureUrl(picture) {
    const P = S.view && S.view.pictures;
    if (!picture || !PICTURE_NAME.test(picture) || !P || !PICTURE_BASE.test(P.base)) return null;
    if (P.ready !== null && !P.ready.includes(picture)) return null;
    return P.base + encodeURIComponent(picture) + '.svg';
  }

  /** The window with the Scene's Picture, or a plain backdrop. */
  function windowEl(picture) {
    const w = el('div', 'window');
    w.dataset.picture = picture || '';
    const url = pictureUrl(picture);
    if (url) {
      const img = el('img');
      img.alt = '';
      img.decoding = 'async';
      img.addEventListener('error', () => { img.hidden = true; });
      img.src = url;
      w.appendChild(img);
    }
    return w;
  }

  /** Show a Picture that finished after its Scene was drawn. */
  function refreshWindow() {
    const w = document.querySelector('#scroll .chapter.current .window');
    if (!w || w.querySelector('img')) return;
    const fresh = windowEl(w.dataset.picture);
    if (fresh.querySelector('img')) w.replaceWith(fresh);
  }

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
      if (current) sec.appendChild(windowEl(ch.scene.picture));
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

  /** The Fight after the first `n` Reports: cards and HP, or null if no Fight is open.
   * Also the Character's HP, from the last hit on the Character. */
  function fightAt(n) {
    const reports = S.view.reports;
    let heroHP = null;
    let start = -1;
    for (let i = 0; i < n; i++) {
      const k = kindOf(reports[i]);
      const d = dataOf(reports[i]);
      if (k === 'damage' && d.defender === null) heroHP = d.hp;
      if (k === 'fightStarts') start = i;
    }
    if (start < 0) return { heroHP, fight: null };
    const fs = dataOf(reports[start]);
    const hero = Object.assign({}, fs.hero);
    const foes = fs.foes.map((f) => Object.assign({}, f));
    let round = 1;
    let over = false;
    let lastHit = null;
    for (let i = start + 1; i < n; i++) {
      const k = kindOf(reports[i]);
      const d = dataOf(reports[i]);
      if (k === 'damage') {
        if (d.defender === null) hero.hp = d.hp;
        else if (foes[d.defender]) foes[d.defender].hp = d.hp;
        lastHit = i;
      }
      if (k === 'round') round = d.n;
      if (k === 'fightWon' || k === 'scene') over = true;
    }
    return { heroHP, fight: over ? null : { start, hero, foes, round, lastHit } };
  }

  // ---------- Cards ----------

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

  /** Make the card of one being. `key` is "hero" or the Creature number. */
  function cardEl(c, key) {
    const hero = key === 'hero';
    const card = el('div', 'card ' + (hero ? 'hero' : 'foe'));
    card.dataset.key = String(key);
    card.append(el('span', 'corner'), el('span', 'corner br'));
    card.append(el('div', 'emblem', hero ? '♦' : '♠'));
    card.append(el('p', 'cname', c.name));
    const gear = el('p', 'cgear', c.weapon + ', ' + c.damage);
    gear.append(document.createElement('br'), 'DR ' + c.dr);
    card.append(gear, hpBar(), el('div', 'hptext'));
    const tag = el('span', 'tag');
    tag.hidden = true;
    card.append(tag);
    return card;
  }

  /** Show the HP of a card. */
  function updateCard(card, c) {
    card.querySelectorAll('.corner').forEach((x) => { x.textContent = String(Math.max(c.hp, 0)); });
    setBar(card.querySelector('.hpbar'), c.hp, c.maxHP);
    card.querySelector('.hptext').textContent = 'HP ' + c.hp + ' / ' + c.maxHP;
    card.classList.toggle('down', c.hp <= 0);
  }

  /** Draw the Fight cards after the first `n` Reports. Returns the Fight, or null. */
  function renderCards(n) {
    const { fight } = fightAt(n);
    if (fight && n === S.view.reports.length && S.view.phase === 'fight') {
      // An admitted world change can replace equipment without starting a new Fight.
      fight.hero = S.view.fight.hero;
      fight.foes = S.view.fight.foes;
      fight.round = S.view.fight.round;
    }
    const box = $('cards');
    if (!fight) {
      $('fight').hidden = true;
      S.cardsFor = -1;
      return null;
    }
    $('fight').hidden = false;
    if (S.cardsFor !== fight.start) {
      box.textContent = '';
      box.appendChild(cardEl(fight.hero, 'hero'));
      fight.foes.forEach((f, i) => box.appendChild(cardEl(f, i)));
      S.cardsFor = fight.start;
    }
    updateCard(box.querySelector('[data-key="hero"]'), fight.hero);
    fight.foes.forEach((f, i) => updateCard(box.querySelector('[data-key="' + i + '"]'), f));
    $('round').textContent = 'Round ' + fight.round;
    return fight;
  }

  /** Shake the card that a hit just landed on. */
  function strike(defender) {
    const key = defender === null ? 'hero' : String(defender);
    const card = document.querySelector('#cards [data-key="' + key + '"]');
    if (!card) return;
    card.classList.remove('struck');
    void card.offsetWidth;
    card.classList.add('struck');
  }

  // ---------- The mat: Choices, Maneuvers, and the end ----------

  function clearTargets() {
    for (const c of document.querySelectorAll('#cards .card')) {
      c.classList.remove('target');
      c.removeAttribute('tabindex');
      c.removeAttribute('role');
      c.onclick = null;
      c.onkeydown = null;
    }
  }

  /** Draw the buttons for the Character's turn. */
  function renderManeuvers() {
    const v = S.view;
    const box = $('maneuvers');
    box.textContent = '';
    clearTargets();
    const hint = $('fight-hint');
    hint.textContent = '';
    if (v.phase !== 'fight' || !v.fight || S.playing || S.busy || v.generation.state === 'running') return;
    const ms = v.fight.maneuvers;
    // Tags with the last Maneuver of each being.
    const heroTag = document.querySelector('#cards [data-key="hero"] .tag');
    if (heroTag) {
      heroTag.textContent = v.fight.hero.maneuver;
      heroTag.hidden = v.fight.hero.maneuver === 'Attack';
    }
    if (S.aim !== null && ms[S.aim]) {
      const m = ms[S.aim];
      hint.textContent = 'Click the Creature to attack.';
      for (const opt of m.options) {
        const card = document.querySelector('#cards [data-key="' + opt.target + '"]');
        if (!card) continue;
        card.classList.add('target');
        card.tabIndex = 0;
        card.setAttribute('role', 'button');
        card.onclick = () => send(opt.input);
        card.onkeydown = (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); send(opt.input); } };
      }
      const chosen = el('button', 'maneuver chosen');
      chosen.type = 'button';
      chosen.append(el('b', '', m.label), el('span', '', m.help));
      chosen.disabled = true;
      const cancel = el('button', 'maneuver cancel');
      cancel.type = 'button';
      cancel.append(el('b', '', 'Cancel'), el('span', '', 'Choose another Maneuver.'));
      cancel.onclick = () => { S.aim = null; renderManeuvers(); };
      box.append(chosen, cancel);
      return;
    }
    hint.textContent = 'Your turn. Choose a Maneuver.';
    ms.forEach((m, idx) => {
      if (m.options.length === 0) return;
      const b = el('button', 'maneuver');
      b.type = 'button';
      b.append(el('b', '', m.label), el('span', '', m.help));
      b.onclick = () => {
        if (m.attacks && m.options.length > 1) {
          S.aim = idx;
          renderManeuvers();
        } else {
          send(m.options[0].input);
        }
      };
      box.appendChild(b);
    });
  }

  /** Draw the Choice buttons, or the end of the Adventure. */
  function renderMat() {
    const v = S.view;
    const choices = $('choices');
    choices.textContent = '';
    $('over').hidden = true;
    $('skip').hidden = !S.playing;
    $('leave').disabled = S.playing || S.busy || v.generation.state === 'running';
    renderCards(S.shown);
    renderManeuvers();
    markState();
    if (S.playing || S.busy || v.generation.state === 'running') return;
    if (v.phase === 'scene' && v.scene) {
      for (const ch of v.scene.choices) {
        if (ch.input === null) continue;
        const b = el('button', 'choice', ch.text);
        b.type = 'button';
        b.onclick = () => send(ch.input);
        choices.appendChild(b);
      }
    }
    if (v.phase === 'ended' || v.phase === 'dead' || (v.phase !== 'title' && v.inputs.length === 0)) {
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
        $('over-text').textContent += ' Play again and \u2190 Adventures start the original Adventure, without your rule changes.';
      }
    }
  }

  // ---------- Character panel ----------

  function renderCharacter() {
    const c = S.view.character;
    const { heroHP } = fightAt(S.shown);
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

  // ---------- Map ----------

  const M = { boxW: 178, boxH: 30, rowH: 60, top: 16, left: 6, qW: 30, qX: 204, qStep: 46 };

  function renderMap() {
    const svg = $('map');
    svg.textContent = '';
    const map = (S.mapView || S.view).map;
    if (map.nodes.length === 0) {
      svg.setAttribute('viewBox', '0 0 300 40');
      const t = svgEl('text', { x: 6, y: 24, class: 'elabel' });
      t.textContent = 'Nothing yet.';
      svg.appendChild(t);
      return;
    }
    const pos = {};
    let maxCol = 0;
    let maxRow = 0;
    for (const n of map.nodes) {
      const y = M.top + n.row * M.rowH;
      const x = n.visited ? M.left : M.qX + (n.col - 1) * M.qStep;
      const w = n.visited ? M.boxW : M.qW;
      pos[n.key] = { x, y, w, h: M.boxH, n };
      maxCol = Math.max(maxCol, n.col);
      maxRow = Math.max(maxRow, n.row);
    }
    const width = Math.max(290, M.qX + Math.max(0, maxCol - 1) * M.qStep + M.qW + 30);
    const height = M.top + (maxRow + 1) * M.rowH;
    svg.setAttribute('viewBox', '0 0 ' + width + ' ' + height);
    svg.setAttribute('width', String(width));

    const edges = svgEl('g');
    const labels = svgEl('g');
    for (const e of map.edges) {
      const a = pos[e.source];
      const b = pos[e.target];
      if (!a || !b) continue;
      let d;
      let lx;
      let ly;
      let anchor = 'middle';
      if (b.n.visited && e.style === 'taken') {
        if (b.n.row > a.n.row) {
          const x = a.x + a.w / 2;
          d = 'M' + x + ' ' + (a.y + a.h) + ' L' + x + ' ' + b.y;
        } else {
          // A path back up the map: go round the left side.
          d = 'M' + a.x + ' ' + (a.y + a.h / 2) + ' C' + (a.x - 30) + ' ' + (a.y + a.h / 2) + ' ' +
            (b.x - 30) + ' ' + (b.y + b.h / 2) + ' ' + b.x + ' ' + (b.y + b.h / 2);
        }
      } else if (b.n.visited) {
        // A dashed branch to a Scene already on the map: go round the right side.
        const sx = a.x + a.w;
        const sy = a.y + a.h / 2;
        const tx = b.x + b.w;
        const ty = b.y + b.h / 2;
        const bulge = 24 + 14 * Math.abs(b.n.row - a.n.row);
        d = 'M' + sx + ' ' + sy + ' C' + (sx + bulge) + ' ' + sy + ' ' + (tx + bulge) + ' ' + ty + ' ' + tx + ' ' + ty;
        lx = sx + 0.75 * bulge + 4;
        ly = (sy + ty) / 2 + 3;
        anchor = 'start';
      } else {
        const sx = a.x + a.w;
        const sy = a.y + a.h / 2;
        if (b.n.col === 1) {
          d = 'M' + sx + ' ' + sy + ' L' + b.x + ' ' + sy;
        } else {
          // Pass under the boxes before it, and come up into this one.
          const bx = b.x + b.w / 2;
          d = 'M' + sx + ' ' + sy + ' C' + (sx + 16) + ' ' + (sy + 24) + ' ' + (bx - 10) + ' ' + (b.y + b.h + 10) +
            ' ' + bx + ' ' + (b.y + b.h);
        }
        lx = b.x + b.w / 2;
        ly = b.y - 4;
      }
      edges.appendChild(svgEl('path', { d, class: 'edge ' + e.style }));
      if (e.label) {
        const t = svgEl('text', { x: lx, y: ly, class: 'elabel', 'text-anchor': anchor });
        t.textContent = e.label;
        labels.appendChild(t);
      }
    }
    svg.appendChild(edges);

    const nodes = svgEl('g');
    for (const key of Object.keys(pos)) {
      const { x, y, w, h, n } = pos[key];
      const cls = ['node', n.visited ? 'scene' : 'unknown'];
      if (n.current) cls.push('current');
      if (n.ending) cls.push('ending');
      if (n.dead) cls.push('dead');
      const g = svgEl('g', { class: cls.join(' ') });
      if (n.current) g.appendChild(svgEl('rect', { x: x - 4, y: y - 4, width: w + 8, height: h + 8, rx: 10, class: 'glow' }));
      g.appendChild(svgEl('rect', { x, y, width: w, height: h, rx: 7 }));
      const t = svgEl('text', { x: x + w / 2, y: y + h / 2 + 4, 'text-anchor': 'middle' });
      const label = n.label.length > 27 ? n.label.slice(0, 26) + '…' : n.label;
      t.textContent = (n.dead ? '☠ ' : '') + label;
      const title = svgEl('title');
      title.textContent = n.visited ? n.label : 'A way you have not taken';
      g.append(t, title);
      nodes.appendChild(g);
    }
    svg.appendChild(nodes);
    svg.appendChild(labels);
  }

  // ---------- Whole page ----------

  /** A line about the Pictures of a live Adventure, or null. */
  function picturesNote(v) {
    const P = v.pictures;
    if (!P || P.ready === null) return null;
    if (P.off) return 'Pictures are off: the Picture check cannot run on this machine.';
    if (P.drawing > 0) return 'The Dungeon Master is drawing the Pictures: ' + P.ready.length + ' done, ' + P.drawing + ' to go.';
    if (P.failed > 0) return P.failed + (P.failed === 1 ? ' Picture' : ' Pictures') + ' failed the check or did not come, so ' + (P.failed === 1 ? 'its Scene shows' : 'their Scenes show') + ' a plain backdrop.';
    return null;
  }

  /** The "New Adventure" tile: a button, or the Wish form, or the steps of the work on a Wish. */
  function renderWish(v) {
    const gen = v.generation;
    const running = gen.state === 'running';
    const showSteps = gen.state !== 'idle';
    const open = showSteps || (S.wishOpen && gen.available);
    $('new-tile').classList.toggle('open', open);
    $('new-open').hidden = open;
    $('new-open').disabled = !gen.available;
    $('new-sub').textContent = gen.available
      ? 'Tell an AI Dungeon Master what you want to play'
      : 'Not available: the Dungeon Master is not connected. Sign in to Codex or Claude Code, or set ANTHROPIC_API_KEY, then run the game again.';
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
    if (ready) {
      $('ready-title').textContent = v.adventure;
      const note = picturesNote(v);
      $('ready-pictures').hidden = note === null;
      $('ready-pictures').textContent = note || '';
    }
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
      } else if (last) {
        li.classList.add('bad');
      }
      list.appendChild(li);
    });
  }

  /** One Adventure card. With `onPlay`, a click starts play; without it, the card is greyed. */
  function adventureCard(c, onPlay, busy, why) {
    const card = el(onPlay ? 'button' : 'div', 'tile adv-card' + (onPlay ? '' : ' failed'));
    if (onPlay) {
      card.type = 'button';
      card.disabled = busy;
      card.onclick = onPlay;
    }
    card.append(el('span', 'card-title', c.title));
    if (c.world) card.append(el('span', 'card-world', c.world));
    if (c.hero) card.append(el('span', 'card-hero', 'You play ' + c.hero));
    if (c.about) card.append(el('span', 'card-about', c.about));
    if (why !== undefined) {
      card.append(el('span', 'card-why', 'Fails the checker now, so you cannot play it: ' + why));
    } else {
      card.append(el('span', 'card-source', c.source));
    }
    return card;
  }

  /** The grid: the "New Adventure" tile, the saved Adventures (newest first), the built-in one,
   * and last the saved Adventures that fail the checker now. */
  function renderGrid(v) {
    const grid = $('grid');
    const busy = v.generation.state === 'running';
    // A poll every 2 seconds must not rebuild the same cards: that would take away keyboard focus
    // and lose a click. So draw again only when the cards change.
    const key = JSON.stringify([v.saved, v.builtin, busy]);
    if (key === S.gridKey && grid.querySelector('.adv-card')) return;
    S.gridKey = key;
    for (const old of grid.querySelectorAll('.adv-card')) old.remove();
    const ok = v.saved.filter((a) => a.ok);
    const bad = v.saved.filter((a) => !a.ok);
    for (const a of ok) grid.appendChild(adventureCard(a, () => startGame('/api/load', { id: a.id }), busy));
    grid.appendChild(adventureCard(v.builtin, () => startGame('/api/builtin'), busy));
    for (const a of bad) grid.appendChild(adventureCard(a, null, busy, a.why || 'it does not read'));
  }

  function renderTitle() {
    const v = S.view;
    $('busy-note').hidden = v.generation.state !== 'running';
    renderWish(v);
    renderGrid(v);
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

  /** In play, a line while the Pictures are still drawing. */
  function showTopPictures(v) {
    const note = picturesNote(v);
    $('top-pictures').hidden = note === null || !(v.pictures && (v.pictures.drawing > 0 || v.pictures.off));
    $('top-pictures').textContent = note || '';
  }

  function renderAll() {
    const v = S.view;
    $('seed').textContent = 'seed ' + v.seed;
    const title = v.phase === 'title';
    $('title-screen').hidden = !title;
    $('table').hidden = title;
    // The seed belongs to a game, so the front page does not show it.
    $('seed').hidden = title;
    document.title = (title ? 'Choose an Adventure' : v.adventure) + ' · Verified RPG';
    if (title) {
      renderTitle();
      markState();
      return;
    }
    $('adventure-title').textContent = v.adventure;
    showTopPictures(v);
    renderStory(S.shown);
    renderMat();
    renderCharacter();
    renderMap();
    renderChange();
  }

  function scrollToMat() {
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
      appendReport(i, true);
      renderMat();
      renderCharacter();
      if (kindOf(r) === 'damage') setTimeout(() => strike(dataOf(r).defender), diceOf(r) && diceOf(r).rolled ? 1000 : 0);
      scrollToMat();
      const k = kindOf(r);
      const dice = diceOf(r);
      await pause(dice ? (dice.rolled ? 1500 : 900) : k === 'scene' ? 700 : 500);
    }
    S.shown = reports.length;
    S.playing = false;
    S.skip = false;
    S.wake = null;
    S.mapView = S.view;
    renderAll();
    const ms = $('maneuvers');
    ms.classList.remove('lit');
    void ms.offsetWidth;
    ms.classList.add('lit');
    scrollToMat();
  }

  let toastTimer = null;
  function toast(text) {
    const t = $('toast');
    t.textContent = text;
    t.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { t.hidden = true; }, 4000);
  }

  /** Send one input, exactly as the server offered it. */
  async function send(input) {
    if (S.busy || S.playing) return;
    S.busy = true;
    S.aim = null;
    if (S.view && S.view.phase !== 'title') renderMat();
    try {
      const { ok, view } = await post('/api/input', input);
      S.view = view;
      if (S.shown > view.reports.length) S.shown = view.reports.length;
      if (!ok) {
        toast(view.error || 'The game refused that input.');
        S.mapView = view;
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
      S.mapView = fresh.view;
      S.shown = 0;
      S.cardsFor = -1;
      S.busy = false;
      if (fresh.view.inputs.length > 0) await send(fresh.view.inputs[0]);
    } catch (e) {
      toast(failText(e));
    } finally {
      S.busy = false;
    }
  }

  /** Send a POST that loads an Adventure, such as a click on its card, then begin it. */
  async function startGame(path, body) {
    if (S.busy || S.playing) return;
    S.busy = true;
    try {
      const { ok, view } = await post(path, body);
      S.view = view;
      S.mapView = view;
      S.shown = view.reports.length;
      S.cardsFor = -1;
      S.wishOpen = false;
      if (!ok || view.phase !== 'title' || view.inputs.length === 0) {
        if (!ok) toast(view.error || 'The game refused that.');
        renderAll();
        // A refused card is drawn again as a grey card, so the focused element is gone.
        if (!ok) focusFront();
        return;
      }
      S.busy = false;
      await send(view.inputs[0]);
    } catch (e) {
      toast(failText(e));
    } finally {
      S.busy = false;
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

  /** Load the game from the server and show it all at once. */
  async function load() {
    try {
      const v = await fetchView();
      S.view = v;
      S.mapView = v;
      S.shown = v.reports.length;
      S.cardsFor = -1;
      renderAll();
      schedulePoll();
    } catch (e) {
      toast(failText(e));
    }
  }

  /** Send a POST that changes the server state: a Wish, Later, a live change, or Cancel. */
  async function action(path, body) {
    if (S.busy || S.playing) return;
    S.busy = true;
    try {
      const { ok, view } = await post(path, body);
      S.view = view;
      S.mapView = view;
      S.shown = view.reports.length;
      S.cardsFor = -1;
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

  /** `true` while the server works in the background: the DM writes or draws. */
  function serverWorking(v) {
    return !!v && (v.generation.state === 'running' || (!!v.pictures && v.pictures.drawing > 0));
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
      // Draw everything again only when it changed: during a live change, the steps change. A
      // redraw on each poll while Pictures draw would rebuild the story every 2 seconds.
      const genChanged = JSON.stringify(v.generation) !== JSON.stringify(S.view.generation);
      if (v.phase === 'title' || !sameGame || genChanged) {
        S.view = v;
        S.mapView = v;
        S.shown = v.reports.length;
        S.cardsFor = -1;
        renderAll();
      } else {
        // In play: take the new list of Pictures, and show a Picture that just finished.
        S.view.pictures = v.pictures;
        showTopPictures(v);
        refreshWindow();
      }
    } catch (e) { /* The server is gone; the next click says so. */ }
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
    startGame('/api/load', { id });
  });
  $('change-send').addEventListener('click', () => {
    const wish = $('change-request').value.trim();
    if (!wish) { toast('Describe the change you want first.'); return; }
    S.aim = null;
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
  // Another tab can move the game on. Catch up when this tab comes back.
  window.addEventListener('focus', async () => {
    if (S.busy || S.playing || !S.view) return;
    try {
      const v = await fetchView();
      // Another tab may have sent a Wish, or started or stopped a live change.
      const wishChanged = JSON.stringify(v.generation) !== JSON.stringify(S.view.generation);
      if (v.seed !== S.view.seed || v.reports.length !== S.view.reports.length || v.phase !== S.view.phase ||
          wishChanged) {
        S.view = v;
        S.mapView = v;
        S.shown = v.reports.length;
        S.cardsFor = -1;
        renderAll();
        schedulePoll();
      }
    } catch (e) { /* The server is gone; the next click says so. */ }
  });

  load();
})();
