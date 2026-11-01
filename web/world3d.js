import * as THREE from './vendor/three.module.js';
import { portalsForView, roomLayout, movePosition, crossedPortal, inputKey, themeFor, figuresForView } from './spatial.js';

const $ = id => document.getElementById(id);
const clamp = (x, lo, hi) => Math.max(lo, Math.min(hi, x));
const motionKeys = new Set(['w', 'a', 's', 'd', 'z', 'q', 'arrowup', 'arrowleft', 'arrowdown', 'arrowright', 'shift']);

/** Spatial input and rendering. Only onChoose can contact the logical engine. */
export class SpatialGame {
  constructor(onChoose) {
    this.onChoose = onChoose;
    this.root = $('world');
    this.canvas = $('world-canvas');
    this.labels = $('world-labels');
    this.scene = new THREE.Scene();
    this.camera = new THREE.PerspectiveCamera(68, 1, 0.1, 180);
    this.camera.rotation.order = 'YXZ';
    this.renderer = new THREE.WebGLRenderer({ canvas: this.canvas, antialias: true, powerPreference: 'high-performance' });
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.7));
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    this.renderer.toneMapping = THREE.ACESFilmicToneMapping;
    this.renderer.toneMappingExposure = 1.25;
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.shadowMap.autoUpdate = false;
    this.scene.add(new THREE.HemisphereLight(0xd6edff, 0x6e6b50, 2.5));
    const sun = new THREE.DirectionalLight(0xffe2b6, 3.2);
    sun.position.set(-10, 18, 8);
    sun.castShadow = true;
    sun.shadow.mapSize.set(1024, 1024);
    sun.shadow.camera.left = sun.shadow.camera.bottom = -18;
    sun.shadow.camera.right = sun.shadow.camera.top = 18;
    sun.shadow.bias = -0.001;
    this.scene.add(sun);
    this.lantern = new THREE.PointLight(0xffd19a, 10, 8, 2);
    this.scene.add(this.lantern);
    this.group = new THREE.Group();
    this.scene.add(this.group);
    this.position = { x: 0, z: 2 };
    this.yaw = 0;
    this.pitch = -0.04;
    this.keys = new Set();
    this.touches = new Map();
    this.active = false;
    this.ready = false;
    this.paused = false;
    this.pending = false;
    this.roomKey = '';
    this.picture = '';
    this.frameTime = 0;
    this.elapsed = 0;
    this.effect = null;
    this.reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
    this.actors = [];
    this.gates = [];
    this.installControls();
    this.resizeObserver = new ResizeObserver(() => this.resize());
    this.resizeObserver.observe(this.root);
    this.renderer.setAnimationLoop(t => this.frame(t));
    this.root.dataset.renderer = 'webgl';
    document.body.classList.add('spatial-mode');
  }

  installControls() {
    const editable = target => target instanceof Element && !!target.closest('input, textarea, select, [contenteditable="true"]');
    window.addEventListener('keydown', e => {
      if (!this.active || editable(e.target) || document.querySelector('dialog[open]')) return;
      const key = e.key.toLowerCase();
      if (key === 'escape') { this.pause(!this.paused); return; }
      if (key === 'j' && !e.repeat) { this.journal(); return; }
      if (this.paused) return;
      if (motionKeys.has(key)) { e.preventDefault(); this.keys.add(key); }
      if (key === 'e' && !e.repeat) { e.preventDefault(); this.useNearest(); }
      if (/^[1-9]$/.test(key) && !e.repeat && this.view?.phase === 'fight') {
        const option = this.layout?.portals[Number(key) - 1];
        if (option) { e.preventDefault(); this.choose(option); }
      }
    });
    window.addEventListener('keyup', e => this.keys.delete(e.key.toLowerCase()));
    window.addEventListener('blur', () => this.keys.clear());
    document.addEventListener('visibilitychange', () => { this.keys.clear(); this.frameTime = 0; });
    let dragging = null;
    this.canvas.addEventListener('pointerdown', e => {
      if (this.paused) return;
      this.canvas.focus({ preventScroll: true });
      dragging = { id: e.pointerId, x: e.clientX, y: e.clientY };
      this.canvas.setPointerCapture(e.pointerId);
    });
    this.canvas.addEventListener('pointermove', e => {
      if (!dragging || dragging.id !== e.pointerId || this.paused) return;
      this.yaw -= (e.clientX - dragging.x) * 0.004;
      this.pitch = clamp(this.pitch - (e.clientY - dragging.y) * 0.003, -0.6, 0.65);
      dragging.x = e.clientX; dragging.y = e.clientY;
    });
    const endDrag = () => { dragging = null; };
    this.canvas.addEventListener('pointerup', endDrag);
    this.canvas.addEventListener('pointercancel', endDrag);
    this.canvas.addEventListener('lostpointercapture', endDrag);
    for (const button of this.root.querySelectorAll('[data-move]')) {
      let pressedAt = 0;
      button.addEventListener('pointerdown', e => {
        e.preventDefault();
        pressedAt = performance.now();
        this.touches.set(e.pointerId, button.dataset.move);
        button.setPointerCapture(e.pointerId);
      });
      button.addEventListener('pointerup', () => {
        if (performance.now() - pressedAt < 160) this.nudge(button.dataset.move);
      });
      button.addEventListener('click', e => { if (e.detail === 0) this.nudge(button.dataset.move); });
      const stop = e => this.touches.delete(e.pointerId);
      button.addEventListener('pointerup', stop);
      button.addEventListener('pointercancel', stop);
      button.addEventListener('lostpointercapture', stop);
    }
    $('world-use').addEventListener('click', () => this.useNearest());
    $('world-pause').addEventListener('click', () => this.pause(!this.paused));
    $('world-resume').addEventListener('click', () => this.pause(false));
    $('world-journal').addEventListener('click', () => this.journal());
    this.canvas.addEventListener('webglcontextlost', e => {
      e.preventDefault();
      this.pause(true);
      $('world-pause-title').textContent = 'The 3D view was interrupted';
      $('world-pause-text').textContent = 'Reload the page to restore it. Your adventure is kept by the server.';
    });
  }

  journal() {
    const open = document.body.classList.toggle('journal-open');
    $('world-journal').setAttribute('aria-expanded', String(open));
    $('world-journal').textContent = open ? 'Close journal' : 'Journal · J';
    if (open) { this.keys.clear(); this.touches.clear(); }
  }

  pause(paused) {
    this.paused = paused;
    this.keys.clear(); this.touches.clear();
    $('world-paused').hidden = !paused;
    $('world-pause').textContent = paused ? 'Resume' : 'Pause';
    if (!paused) this.canvas.focus({ preventScroll: true });
  }

  resize() {
    const width = this.root.clientWidth;
    const height = this.root.clientHeight;
    if (!width || !height) return;
    this.renderer.setSize(width, height, false);
    this.camera.aspect = width / height;
    this.camera.updateProjectionMatrix();
  }

  material(color, options = {}) {
    return new THREE.MeshStandardMaterial({ color, roughness: 0.9, ...options });
  }

  mesh(geometry, material, x, y, z, parent = this.group) {
    const mesh = new THREE.Mesh(geometry, material);
    mesh.position.set(x, y, z);
    mesh.receiveShadow = true;
    mesh.castShadow = true;
    parent.add(mesh);
    return mesh;
  }

  box(w, h, d, material, x, y, z, parent) {
    return this.mesh(new THREE.BoxGeometry(w, h, d), material, x, y, z, parent);
  }

  clearRoom() {
    const geometries = new Set(), materials = new Set(), textures = new Set();
    this.group.traverse(obj => {
      if (obj.geometry) geometries.add(obj.geometry);
      const list = Array.isArray(obj.material) ? obj.material : [obj.material];
      for (const mat of list) if (mat) {
        materials.add(mat);
        if (mat.map) textures.add(mat.map);
      }
    });
    geometries.forEach(g => g.dispose());
    materials.forEach(m => m.dispose());
    textures.forEach(t => t.dispose());
    this.group.clear();
    this.labels.replaceChildren();
    this.gates = []; this.actors = [];
    this.picture = '';
    this.pictureMesh = null;
  }

  buildRoom(view, layout, pictureURL) {
    this.buildStarted = performance.now();
    this.clearRoom();
    const theme = themeFor(view);
    this.theme = theme;
    this.scene.background = new THREE.Color(theme.sky);
    this.scene.fog = new THREE.Fog(theme.sky, layout.radius + 15, layout.radius + 80);
    const ground = this.material(theme.ground);
    const stone = this.material(theme.stone);
    const dark = this.material(0x283735);
    const brass = this.material(theme.glow, { metalness: 0.6, roughness: 0.3 });
    const r = layout.radius;
    this.mesh(new THREE.CylinderGeometry(r + 1.8, r + 3, 1, 64), ground, 0, -0.55, 0);
    this.mesh(new THREE.CylinderGeometry(r + 3, r + 6, 4, 32), dark, 0, -3, 0);
    const ocean = this.material(theme.name === 'Dunes' ? 0xbfa16c : theme.nature ? 0x2c4943 : 0x294d62, { roughness: 0.6 });
    this.mesh(new THREE.CylinderGeometry(160, 160, 0.3, 64), ocean, 0, -5.5, 0);
    // Etched floor rings and a compass. Every ornament on the floor is non-blocking.
    for (const radius of [2.2, r * 0.65, r + 0.8]) {
      const ring = this.mesh(new THREE.RingGeometry(radius, radius + 0.035, 96),
        this.material(0xc6b991, { transparent: true, opacity: 0.35 }), 0, 0.008, 0);
      ring.rotation.x = -Math.PI / 2;
      ring.castShadow = false;
    }
    for (let i = 0; i < 12; i++) {
      const a = i * Math.PI / 6;
      const line = this.box(0.025, 0.012, r - 2.4, stone,
        Math.sin(a) * (r + 2.4) / 2, 0.005, Math.cos(a) * (r + 2.4) / 2);
      line.rotation.y = a;
    }
    const center = this.mesh(new THREE.CylinderGeometry(0.42, 0.42, 0.02, 6), brass, 0, 0.02, 0);
    center.castShadow = false;
    // Continuous outer curb, outside the convex navigable disc.
    for (let i = 0; i < 64; i++) {
      const a = i * Math.PI * 2 / 64;
      const curb = this.box(0.7, 0.45, 0.45, stone, Math.sin(a) * (r + 1.25), 0.2, Math.cos(a) * (r + 1.25));
      curb.rotation.y = a;
    }
    // Scenery is outside the walkable floor; it cannot hide or block a choice.
    for (let i = 0; i < 24; i++) {
      const a = i * 2.399963;
      const distance = r + 6 + (i % 5) * 2.5;
      const x = Math.sin(a) * distance, z = Math.cos(a) * distance;
      if (theme.name === 'Dunes') {
        const dune = this.mesh(new THREE.SphereGeometry(3.5 + i % 3, 12, 6), ground, x, -1.8, z);
        dune.scale.set(1.7, 0.55, 1);
        if (i % 4 === 0) {
          this.mesh(new THREE.CylinderGeometry(0.13, 0.23, 3.8, 7), this.material(0x80603b), x, 1.5, z);
          for (let leaf = 0; leaf < 5; leaf++) {
            const frond = this.mesh(new THREE.ConeGeometry(0.5, 3, 5), this.material(0x6b8252), x, 3.5, z);
            frond.rotation.set(1.05, leaf * Math.PI * 2 / 5, 0);
          }
        }
      } else if (theme.nature) {
        this.mesh(new THREE.CylinderGeometry(0.18, 0.35, 4, 7), this.material(0x604b3d), x, 0.6, z);
        this.mesh(new THREE.ConeGeometry(2.4, 6, 7), this.material(i % 2 ? 0x284c3c : 0x3b6250), x, 4, z);
      } else {
        const rock = this.mesh(new THREE.DodecahedronGeometry(2 + i % 4), this.material(i % 2 ? 0x566b74 : 0x718087), x, -1.4, z);
        rock.rotation.set(i * 0.7, i, i * 0.4);
        rock.scale.y = 1.5 + i % 3;
      }
    }
    if (theme.name === 'Dunes') {
      // Monument silhouettes remain outside the navigable graph realization.
      for (const [x, z, size] of [[-r - 9, -r - 15, 11], [r + 10, -r - 24, 15], [r + 22, -r - 14, 7]]) {
        const pyramid = this.mesh(new THREE.ConeGeometry(size, size * 1.15, 4), stone, x, size * 0.575 - 1, z);
        pyramid.rotation.y = Math.PI / 4;
      }
      for (let i = 0; i < 6; i++) {
        const x = (i - 2.5) * 2.4;
        this.mesh(new THREE.CylinderGeometry(0.4, 0.5, 3.6, 10), stone, x, 1.6, r + 5);
        this.box(1.15, 0.35, 1.15, stone, x, 3.55, r + 5);
      }
    }
    const figures = figuresForView(view);
    for (const p of layout.portals) this.buildObject(p, stone, brass, figures);
    // A painted scene is a decorative mural only, using the existing checked URL.
    const wall = new THREE.Group();
    wall.position.set(0, 0, r + 0.35);
    wall.rotation.y = Math.PI;
    this.group.add(wall);
    this.box(5.8, 3.9, 0.35, stone, 0, 2, 0, wall);
    this.pictureMesh = this.mesh(new THREE.PlaneGeometry(5.3, 3.3),
      this.material(0x283e47), 0, 2, 0.19, wall);
    this.loadPicture(pictureURL);
    const hasConversation = layout.portals.some(p => p.visual.type === 'person');
    figures.forEach((figure, i) => {
      if (hasConversation && i === 0) return; // This person is already at their dialogue interaction.
      const x = (i - (figures.length - 1) / 2) * 2.1;
      this.buildActor(figure, x, -3, i);
    });
    this.root.dataset.portalCount = String(layout.portals.length);
    this.root.dataset.npcCount = String(figures.length || Number(hasConversation));
    this.renderer.shadowMap.needsUpdate = true;
    this.root.dataset.buildMs = (performance.now() - this.buildStarted).toFixed(2);
    this.awaitingFirstFrame = true;
  }

  buildObject(p, stone, brass, figures) {
    const group = new THREE.Group();
    group.position.set(p.x, 0, p.z);
    group.rotation.y = -p.angle;
    this.group.add(group);
    const tint = p.kind === 'attack' ? 0xf18c75 : p.kind === 'defense' ? 0x83d6c1 : this.theme.glow;
    const wood = this.material(0x785135), paleWood = this.material(0xb68855);
    const metal = this.material(0xc0ccd0, { metalness: 0.7, roughness: 0.3 });
    const type = p.visual.type;
    if (type === 'person') {
      const figure = figures[0] || { name: 'Traveller', alive: true, combat: false };
      this.buildActor(figure, 0, -0.3, 0, group);
    } else if (type === 'ladder') {
      this.mesh(new THREE.DodecahedronGeometry(1.3, 0), stone, 0, 0.9, -0.8, group);
      for (const side of [-1, 1]) {
        const rail = this.box(0.12, 3.3, 0.15, paleWood, side * 0.53, 1.6, 0, group);
        rail.rotation.x = -0.16;
      }
      for (let i = 0; i < 9; i++) this.box(1.1, 0.1, 0.16, wood, 0, 0.25 + i * 0.34, 0.22 - i * 0.052, group);
    } else if (type === 'stairs') {
      for (let i = 0; i < 5; i++) this.box(1.8, 0.3 * (i + 1), 0.5, stone, 0, 0.15 * (i + 1), 1 - i * 0.5, group);
    } else if (type === 'boat' || type === 'water') {
      const water = this.mesh(new THREE.CylinderGeometry(1.65, 1.65, 0.025, 36),
        this.material(0x428a9c, { metalness: 0.35, roughness: 0.22 }), 0, 0.025, 0, group);
      water.scale.z = 1.2;
      if (type === 'boat') {
        this.box(1.1, 0.22, 2.5, wood, 0, 0.23, 0, group);
        for (const side of [-1, 1]) {
          this.box(0.16, 0.55, 2.6, paleWood, side * 0.58, 0.5, 0, group);
          const bow = this.box(0.15, 0.48, 1, wood, side * 0.29, 0.48, -1.6, group);
          bow.rotation.y = side * -0.65;
          this.box(1.1, 0.12, 0.32, paleWood, 0, 0.55, side * 0.6, group);
        }
        const oar = this.box(2.8, 0.07, 0.12, paleWood, 0.3, 0.8, 0.1, group);
        oar.rotation.y = 0.4;
      } else {
        for (let i = 0; i < 4; i++) this.mesh(new THREE.CylinderGeometry(0.25, 0.3, 0.15, 7), stone, (i % 2 ? 0.28 : -0.28), 0.12, 1.3 - i * 0.7, group);
      }
    } else if (type === 'door' || type === 'window') {
      const height = type === 'door' ? 2.65 : 2.1;
      for (const side of [-1, 1]) this.box(0.3, height, 0.45, stone, side * 0.95, height / 2, 0, group);
      this.box(2.2, 0.25, 0.45, stone, 0, height, 0, group);
      if (type === 'door') {
        for (let i = 0; i < 6; i++) this.box(0.27, 2.5, 0.18, i % 2 ? wood : paleWood, -0.7 + i * 0.28, 1.25, 0, group);
        this.mesh(new THREE.TorusGeometry(0.1, 0.025, 6, 12), brass, 0.55, 1.2, 0.14, group);
      } else {
        this.box(1.8, 0.25, 0.5, paleWood, 0, 0.75, 0, group);
        this.box(0.08, 1.2, 0.12, wood, 0, 1.4, 0, group);
      }
    } else if (type === 'lookout') {
      for (let i = 0; i < 3; i++) {
        const leg = this.box(0.07, 1.4, 0.07, wood, Math.cos(i * 2.094) * 0.3, 0.65, Math.sin(i * 2.094) * 0.3, group);
        leg.rotation.z = Math.cos(i * 2.094) * 0.25;
        leg.rotation.x = -Math.sin(i * 2.094) * 0.25;
      }
      const telescope = this.mesh(new THREE.CylinderGeometry(0.17, 0.23, 1.3, 12), brass, 0, 1.5, 0, group);
      telescope.rotation.x = Math.PI / 2 - 0.3;
      this.mesh(new THREE.SphereGeometry(0.18, 12, 8), this.material(0x75b3c5), 0, 1.69, -0.6, group);
    } else if (type === 'chest') {
      this.box(1.6, 0.75, 0.95, wood, 0, 0.4, 0, group);
      this.box(1.65, 0.2, 1, paleWood, 0, 0.9, 0, group);
      for (const side of [-1, 1]) this.box(0.12, 0.95, 1.02, brass, side * 0.55, 0.5, 0, group);
      this.box(0.2, 0.25, 0.06, brass, 0, 0.7, 0.54, group);
    } else if (type === 'sword') {
      this.mesh(new THREE.DodecahedronGeometry(0.7, 0), stone, 0, 0.2, 0, group);
      this.box(0.16, 1.4, 0.07, metal, 0, 1.05, 0, group);
      this.box(0.7, 0.1, 0.15, brass, 0, 1.7, 0, group);
      this.box(0.13, 0.45, 0.13, wood, 0, 1.95, 0, group);
      this.mesh(new THREE.IcosahedronGeometry(0.12), brass, 0, 2.2, 0, group);
    } else if (type === 'shield') {
      const shield = this.mesh(new THREE.CylinderGeometry(0.75, 0.75, 0.16, 8), metal, 0, 1.1, 0, group);
      shield.rotation.x = Math.PI / 2;
      this.mesh(new THREE.SphereGeometry(0.2, 8, 8), brass, 0, 1.1, 0.13, group);
      this.box(0.12, 1.8, 0.14, wood, 0, 0.9, -0.18, group);
    } else if (type === 'lantern' || type === 'camp') {
      if (type === 'lantern') {
        this.box(0.15, 1.8, 0.15, wood, 0, 0.9, 0, group);
        this.box(0.65, 0.85, 0.65, brass, 0, 1.9, 0, group);
        this.box(0.52, 0.65, 0.68, this.material(0xffd98a, { emissive: 0xffb641, emissiveIntensity: 1 }), 0, 1.9, 0, group);
      } else {
        for (const sign of [-1, 1]) {
          const log = this.box(1.3, 0.2, 0.2, wood, 0, 0.12, 0, group);
          log.rotation.y = sign * 0.6;
        }
        this.mesh(new THREE.ConeGeometry(0.3, 0.8, 6), this.material(0xffb04c, { emissive: 0xee6429 }), 0, 0.5, 0, group);
      }
    } else {
      // A real trail, with a direction sign, rather than a generic portal.
      for (let i = 0; i < 7; i++) {
        const slab = this.mesh(new THREE.CylinderGeometry(0.48, 0.5, 0.06, 6), stone, Math.sin(i) * 0.24, 0.025, 1.4 - i * 0.48, group);
        slab.scale.z = 0.7;
      }
      this.box(0.12, 1.6, 0.12, wood, 0.95, 0.8, -0.5, group);
      this.box(1.05, 0.38, 0.12, paleWood, 0.95, 1.5, -0.5, group);
      const arrow = this.mesh(new THREE.ConeGeometry(0.27, 0.4, 3), paleWood, 1.63, 1.5, -0.5, group);
      arrow.rotation.z = -Math.PI / 2;
    }
    const circle = this.mesh(new THREE.RingGeometry(0.82, 0.86, 48),
      new THREE.MeshBasicMaterial({ color: tint, side: THREE.DoubleSide, transparent: true, opacity: 0.65 }), 0, 0.065, 0, group);
    circle.rotation.x = -Math.PI / 2;
    circle.castShadow = false;
    const label = document.createElement('div');
    label.className = 'portal-label';
    label.dataset.portal = String(p.index);
    label.dataset.object = type;
    const number = document.createElement('span');
    number.className = 'portal-number';
    number.textContent = String(p.index + 1).padStart(2, '0') + ' · ' + (type === 'person' ? 'Talk' : type);
    const title = document.createElement('span');
    title.textContent = p.label;
    label.append(number, title);
    this.labels.appendChild(label);
    this.gates.push({ ...p, label, ring: circle });
  }

  buildActor(foe, x, z, index, parent = this.group) {
    const actor = new THREE.Group();
    actor.position.set(x, 0, z);
    parent.add(actor);
    const napoleon = /Napol|Bonaparte/.test(foe.name);
    const body = this.material(napoleon ? 0x243f62 : foe.combat ? 0x70473b : index % 2 ? 0x526c77 : 0x777850);
    const metal = this.material(0x939a9e, { metalness: 0.65, roughness: 0.35 });
    const isWolf = /wolf|loup|hound|dog/i.test(foe.name);
    if (isWolf) {
      const fur = this.material(0x7a8588), dark = this.material(0x273339);
      const torso = this.mesh(new THREE.IcosahedronGeometry(0.65, 1), fur, 0, 0.8, 0, actor);
      torso.scale.set(0.65, 0.7, 1.3);
      this.mesh(new THREE.IcosahedronGeometry(0.38, 0), fur, 0, 1.15, 0.7, actor);
      this.box(0.32, 0.22, 0.4, fur, 0, 1.05, 1, actor);
      this.box(0.2, 0.13, 0.1, dark, 0, 1.08, 1.23, actor);
      for (const side of [-1, 1]) {
        this.mesh(new THREE.ConeGeometry(0.13, 0.35, 4), fur, side * 0.22, 1.5, 0.65, actor);
        this.box(0.06, 0.06, 0.04, this.material(0xf5d185), side * 0.22, 1.24, 0.98, actor);
        for (const end of [-1, 1]) this.box(0.15, 0.6, 0.18, fur, side * 0.3, 0.3, end * 0.5, actor);
      }
      const tail = this.mesh(new THREE.ConeGeometry(0.17, 0.85, 7), fur, 0, 0.75, -1, actor);
      tail.rotation.x = -1.1;
    } else {
      const skin = this.material(/goblin/i.test(foe.name) ? 0x7c9c68 : 0xd5aa86);
      this.mesh(new THREE.CapsuleGeometry(0.35, 0.65, 4, 8), body, 0, 1.1, 0, actor);
      this.mesh(new THREE.IcosahedronGeometry(0.29, 1), skin, 0, 1.9, 0, actor);
      this.mesh(new THREE.SphereGeometry(0.3, 8, 6, 0, Math.PI * 2, 0, Math.PI / 2), this.material(0x493c35), 0, 1.96, 0, actor);
      if (napoleon) {
        const black = this.material(0x20272c), gold = this.material(0xd8b35f);
        const hat = this.mesh(new THREE.SphereGeometry(0.45, 8, 4), black, 0, 2.17, 0, actor);
        hat.scale.set(1.6, 0.45, 0.7);
        for (const side of [-1, 1]) this.box(0.2, 0.08, 0.3, gold, side * 0.4, 1.48, 0, actor);
        for (let i = 0; i < 3; i++) this.mesh(new THREE.SphereGeometry(0.035, 6, 4), gold, 0.1, 1.4 - i * 0.17, 0.34, actor);
      }
      for (const side of [-1, 1]) this.box(0.05, 0.05, 0.03, this.material(0x283039), side * 0.1, 1.94, 0.26, actor);
      for (const side of [-1, 1]) {
        this.box(0.22, 0.6, 0.24, body, side * 0.2, 0.35, 0, actor);
        this.box(0.18, 0.65, 0.2, body, side * 0.43, 1.1, 0, actor);
        this.mesh(new THREE.IcosahedronGeometry(0.12), skin, side * 0.43, 0.74, 0, actor);
      }
      if (foe.combat || /wrecker|Hollis|ruffian/i.test(foe.name)) {
      this.box(0.07, 1.2, 0.1, metal, 0.55, 1.2, 0.3, actor);
      this.box(0.42, 0.08, 0.13, metal, 0.55, 0.77, 0.3, actor);
      }
    }
    if (!foe.alive) { actor.rotation.z = Math.PI / 2; actor.position.y = 0.3; }
    const label = document.createElement('div');
    label.className = 'actor-label';
    label.dataset.actor = foe.name;
    label.textContent = foe.name + (foe.combat ? ' · ' + Math.max(0, foe.hp) + ' HP' : '');
    this.labels.appendChild(label);
    this.actors.push({ mesh: actor, alive: foe.alive, index, combat: foe.combat, label, name: foe.name, x, z });
  }

  /** Animate only events received from Lean. Geometry never computes combat outcomes. */
  presentReport(report) {
    const kind = typeof report === 'string' ? report : Object.keys(report)[0];
    const data = typeof report === 'string' ? {} : report[kind];
    this.effect = { kind, data, started: this.elapsed };
    if ((kind === 'damage' && data.injury > 0) || kind === 'attack') {
      const hit = $('world-hit');
      hit.className = 'world-hit';
      void hit.offsetWidth;
      hit.classList.add(kind === 'damage' && data.defender === null ? 'hurt' : 'strike');
    }
  }

  combatActions(view, portals) {
    const dock = $('world-combat-actions');
    dock.hidden = view.phase !== 'fight' || !portals.length;
    const key = JSON.stringify(portals.map(p => [p.key, p.label, p.detail]));
    if (key === this.actionKey) return;
    this.actionKey = key;
    dock.replaceChildren();
    portals.forEach((option, i) => {
      const button = document.createElement('button');
      button.type = 'button';
      button.textContent = (i < 9 ? (i + 1) + ' · ' : '') + option.label;
      button.title = option.detail || option.label;
      button.dataset.inputKey = option.key;
      button.className = option.kind;
      button.addEventListener('click', () => this.choose(option));
      dock.appendChild(button);
    });
  }

  loadPicture(url) {
    if (!url || url === this.picture || !this.pictureMesh) return;
    this.picture = url;
    const target = this.pictureMesh;
    new THREE.TextureLoader().load(url, texture => {
      if (this.pictureMesh !== target) { texture.dispose(); return; }
      texture.colorSpace = THREE.SRGBColorSpace;
      if (target.material.map) target.material.map.dispose();
      target.material.map = texture;
      target.material.color.set(0xffffff);
      target.material.needsUpdate = true;
    }, undefined, () => { /* The mural is optional; interactions do not depend on it. */ });
  }

  /** Synchronize from the authoritative view; polling does not reset the camera. */
  update(view, ready, pictureURL) {
    this.view = view;
    this.active = view.phase !== 'title';
    this.root.hidden = !this.active;
    if (!this.active) {
      this.keys.clear(); this.touches.clear();
      this.roomKey = '';
      this.pending = false;
      this.pause(false);
      return;
    }
    this.ready = ready;
    const portals = portalsForView(view);
    this.combatActions(view, portals);
    const visits = view.reports.filter(r => r && typeof r === 'object' && r.scene).length;
    const roomKey = JSON.stringify([view.seed, view.adventure, view.scene?.id, visits, view.phase, portals.map(p => p.key)]);
    if (roomKey !== this.roomKey) {
      const samePlace = this.placeKey === JSON.stringify([view.seed, view.adventure, view.scene?.id, visits, view.phase]);
      this.roomKey = roomKey;
      this.placeKey = JSON.stringify([view.seed, view.adventure, view.scene?.id, visits, view.phase]);
      this.layout = roomLayout(portals);
      this.buildRoom(view, this.layout, pictureURL);
      if (!samePlace) {
        this.position = { ...this.layout.spawn };
        this.yaw = 0; this.pitch = -0.04;
        this.keys.clear(); this.touches.clear();
      } else {
        this.position = movePosition(this.position, 0, 0, this.layout.bound);
      }
      this.resize();
    } else {
      this.loadPicture(pictureURL);
      if (view.fight) this.actors.filter(a => a.combat).forEach(a => {
        a.alive = !!view.fight.foes[a.index]?.alive;
        a.mesh.rotation.z = a.alive ? 0 : Math.PI / 2;
        a.mesh.position.y = a.alive ? 0 : 0.3;
        a.label.textContent = a.name + ' · ' + Math.max(0, view.fight.foes[a.index]?.hp || 0) + ' HP';
      });
    }
    $('world-location').textContent = view.scene?.title || view.adventure;
    $('world-description').textContent = view.phase === 'fight'
      ? 'Choose a maneuver below, press its number, or approach a weapon. Watch the dice resolve attacks, dodges and damage.'
      : (view.scene?.text || '');
    $('world-mode').textContent = view.phase === 'fight' ? 'Combat · round ' + view.fight.round
      : view.phase === 'dead' ? 'Adventure over' : view.phase === 'ended' ? 'Journey complete' : 'Explore · ' + portals.length + (portals.length === 1 ? ' interaction' : ' interactions');
    $('world-hp').textContent = view.character.name + ' · ' + Math.max(0, view.character.hp) + ' / ' + view.character.maxHP + ' HP';
    $('world-loading').hidden = ready;
    this.root.dataset.phase = view.phase;
    this.root.dataset.ready = String(ready && !this.pending);
    const ended = ['ended', 'dead'].includes(view.phase) || view.inputs.length === 0;
    document.body.classList.toggle('game-ended', ended);
  }

  nearest() {
    let nearest = null, distance = 2.1;
    for (const p of this.layout?.portals || []) {
      const d = Math.hypot(this.position.x - p.x, this.position.z - p.z);
      if (d < distance) { nearest = p; distance = d; }
    }
    return nearest;
  }

  useNearest() {
    const p = this.nearest();
    if (p) this.choose(p);
  }

  canMove() {
    return this.active && this.ready && !this.pending && !this.paused && !document.querySelector('dialog[open]');
  }

  move(dx, dz) {
    if (!this.canMove() || !this.layout) return;
    const next = movePosition(this.position, dx, dz, this.layout.bound);
    const selected = crossedPortal(this.position, next, this.layout.portals);
    this.position = next;
    if (selected) this.choose(selected);
  }

  nudge(direction) {
    const forward = Number(direction === 'arrowup') - Number(direction === 'arrowdown');
    const right = Number(direction === 'arrowright') - Number(direction === 'arrowleft');
    this.move((-Math.sin(this.yaw) * forward + Math.cos(this.yaw) * right) * 0.55,
      (-Math.cos(this.yaw) * forward - Math.sin(this.yaw) * right) * 0.55);
  }

  async choose(portal) {
    if (!this.ready || this.paused || this.pending || !this.active) return;
    // Re-check against the latest view, never a captured destination or old portal.
    if (!this.view.inputs.some(i => inputKey(i) === portal.key)) return;
    this.pending = true;
    this.keys.clear(); this.touches.clear();
    try { await this.onChoose(portal.input); }
    finally {
      this.pending = false;
      this.root.dataset.ready = String(this.ready);
    }
  }

  frame(time) {
    const dt = this.frameTime ? Math.min((time - this.frameTime) / 1000, 0.05) : 0;
    this.frameTime = time;
    if (!this.active || document.hidden || !this.layout) return;
    this.elapsed += dt;
    const canMove = this.canMove();
    let moving = false;
    if (canMove) {
      const has = (...keys) => keys.some(k => this.keys.has(k) || [...this.touches.values()].includes(k));
      let forward = Number(has('w', 'z', 'arrowup')) - Number(has('s', 'arrowdown'));
      let right = Number(has('d', 'arrowright')) - Number(has('a', 'q', 'arrowleft'));
      const length = Math.hypot(forward, right);
      moving = length > 0;
      if (moving) {
        forward /= length; right /= length;
        const speed = has('shift') ? 6.2 : 3.5;
        const dx = (-Math.sin(this.yaw) * forward + Math.cos(this.yaw) * right) * speed * dt;
        const dz = (-Math.cos(this.yaw) * forward - Math.sin(this.yaw) * right) * speed * dt;
        this.move(dx, dz);
      }
    }
    const reduced = this.reducedMotion.matches;
    for (const button of $('world-combat-actions').children) button.disabled = !canMove;
    this.camera.position.set(this.position.x, 1.7 + (moving && !reduced ? Math.sin(this.elapsed * 11) * 0.025 : 0), this.position.z);
    this.camera.rotation.set(this.pitch, this.yaw, 0);
    this.camera.updateMatrixWorld();
    this.lantern.position.copy(this.camera.position);
    this.lantern.position.y -= 0.3;
    const near = this.nearest();
    $('world-prompt').hidden = !near || !canMove;
    $('world-use').disabled = !near || !canMove;
    if (near) {
      $('world-choice').textContent = near.label;
      $('world-detail').textContent = near.detail || 'Approach the marked object to interact, or press E here.';
    }
    for (const gate of this.gates) {
      const point = new THREE.Vector3(gate.x, 2.3, gate.z).project(this.camera);
      const visible = point.z > -1 && point.z < 1 && Math.abs(point.x) < 1.15 && Math.abs(point.y) < 1.3;
      gate.label.hidden = !visible;
      if (visible) {
        gate.label.style.left = ((point.x + 1) * 50) + '%';
        gate.label.style.top = ((1 - point.y) * 50) + '%';
        gate.label.classList.toggle('near', near?.key === gate.key);
      }
      gate.ring.material.opacity = near?.key === gate.key ? 1 : 0.55;
    }
    for (const actor of this.actors) {
      const age = this.effect ? this.elapsed - this.effect.started : 10;
      const pulse = age < 0.6 && !reduced ? Math.sin(Math.PI * Math.min(1, age / 0.6)) : 0;
      const attacking = this.effect?.kind === 'attack' && this.effect.data.attacker === actor.index;
      const hurt = this.effect?.kind === 'damage' && this.effect.data.injury > 0 && this.effect.data.defender === actor.index;
      actor.mesh.position.z = actor.z + (attacking ? pulse * 0.75 : 0);
      actor.mesh.position.x = actor.x + (hurt ? Math.sin(age * 45) * pulse * 0.09 : 0);
      if (actor.alive) actor.mesh.position.y = reduced ? 0 : Math.sin(this.elapsed * 2 + actor.index) * 0.03;
      actor.label.classList.toggle('taking-hit', !!hurt && pulse > 0);
      const point = actor.mesh.localToWorld(new THREE.Vector3(0, 2.35, 0)).project(this.camera);
      actor.label.hidden = point.z < -1 || point.z > 1 || Math.abs(point.x) > 1 || Math.abs(point.y) > 1;
      actor.label.style.left = ((point.x + 1) * 50) + '%';
      actor.label.style.top = ((1 - point.y) * 50) + '%';
    }
    // Presentation coordinates let navigation tests observe movement without controlling it.
    this.root.dataset.playerX = this.position.x.toFixed(3);
    this.root.dataset.playerZ = this.position.z.toFixed(3);
    this.renderer.render(this.scene, this.camera);
    if (this.awaitingFirstFrame) {
      this.root.dataset.firstFrameMs = (performance.now() - this.buildStarted).toFixed(2);
      this.awaitingFirstFrame = false;
    }
  }
}
