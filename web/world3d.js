import * as THREE from './vendor/three.module.js';
import { portalsForView, inputKey, themeFor, figuresForView, interactionPoints, nearestPoint, pointRadius } from './spatial.js';
import { environmentFor, placeForScene, eventAnchorForScene, worldLayout, sceneryFor, propRadius, moveInWorld } from './environment.js';
import { arrivalForLayout, planTransition, transitionAt, DEFAULT_PITCH } from './travel.js';
import { storyTimeline } from './story.js';
import { hasResultToRead } from './playback.js';

const $ = id => document.getElementById(id);
const clamp = (x, lo, hi) => Math.max(lo, Math.min(hi, x));
const choiceCount = n => n + (n === 1 ? ' choice' : ' choices');
const motionKeys = new Set(['w', 'a', 's', 'd', 'z', 'q', 'arrowup', 'arrowleft', 'arrowdown', 'arrowright', 'shift']);

/** The 3D world. It draws the view and walks the Player. Only `onChoose` sends an input to the
 * server, and it sends an input that the current view offers, unchanged. */
export class SpatialGame {
  constructor(onChoose) {
    this.onChoose = onChoose;
    this.root = $('world');
    this.canvas = $('world-canvas');
    this.labels = $('world-labels');
    this.scene = new THREE.Scene();
    this.camera = new THREE.PerspectiveCamera(68, 1, 0.1, 500);
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
    sun.position.set(-90, 160, 80);
    sun.castShadow = true;
    sun.shadow.mapSize.set(2048, 2048);
    sun.shadow.camera.left = sun.shadow.camera.bottom = -130;
    sun.shadow.camera.right = sun.shadow.camera.top = 130;
    sun.shadow.camera.far = 400;
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
    this.travel = null;
    this.travelSceneKey = '';
    this.roomKey = '';
    this.frameTime = 0;
    this.elapsed = 0;
    this.effect = null;
    this.reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');
    this.actors = [];
    this.points = [];
    this.portals = [];
    this.selectedId = null;
    this.raycaster = new THREE.Raycaster();
    this.installControls();
    this.resizeObserver = new ResizeObserver(() => this.resize());
    this.resizeObserver.observe(this.root);
    $('world-description').addEventListener('click', () => this.finishStory());
    $('world-continue-button').addEventListener('click', () => this.continueOn());
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
      if (motionKeys.has(key)) {
        e.preventDefault();
        // A held key from the previous choice must be released before moving again.
        if (e.repeat && !this.keys.has(key)) return;
        // During a transition to the next Scene, or while it waits for Continue, the Player cannot move.
        if (this.travel || this.waiting) return;
        this.keys.add(key);
      }
      if (this.waiting && ['enter', ' ', 'e'].includes(key) && !e.repeat) { e.preventDefault(); this.continueOn(); return; }
      if (key === 'e' && !e.repeat) { e.preventDefault(); this.useNearest(); }
      if (/^[1-9]$/.test(key) && !e.repeat) {
        const options = this.view?.phase === 'fight' ? this.portals : this.menuPoint()?.actions || [];
        const option = options[Number(key) - 1];
        if (option) { e.preventDefault(); this.choose(option); }
      }
    });
    window.addEventListener('keyup', e => this.keys.delete(e.key.toLowerCase()));
    window.addEventListener('blur', () => this.keys.clear());
    document.addEventListener('visibilitychange', () => { this.keys.clear(); this.frameTime = 0; });
    // A reload keeps the last position, even one reached since the last save.
    window.addEventListener('pagehide', () => { if (this.active && this.storageKey && !this.travel) this.savePosition(); });
    let dragging = null;
    this.canvas.addEventListener('pointerdown', e => {
      if (this.paused) return;
      this.canvas.focus({ preventScroll: true });
      dragging = { id: e.pointerId, x: e.clientX, y: e.clientY, startX: e.clientX, startY: e.clientY, at: performance.now() };
      this.canvas.setPointerCapture(e.pointerId);
    });
    this.canvas.addEventListener('pointermove', e => {
      if (!dragging || dragging.id !== e.pointerId || this.paused || this.travel) return;
      this.yaw -= (e.clientX - dragging.x) * 0.004;
      this.pitch = clamp(this.pitch - (e.clientY - dragging.y) * 0.003, -0.6, 0.65);
      dragging.x = e.clientX; dragging.y = e.clientY;
    });
    const endDrag = () => { dragging = null; };
    this.canvas.addEventListener('pointerup', e => {
      // A short press with no drag is a click: it selects the person or object under the pointer.
      if (dragging && Math.hypot(e.clientX - dragging.startX, e.clientY - dragging.startY) < 6
        && performance.now() - dragging.at < 500) this.selectAt(e.clientX, e.clientY);
      endDrag();
    });
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
    $('world-pause').addEventListener('click', () => this.pause(!this.paused));
    $('world-resume').addEventListener('click', () => this.pause(false));
    $('world-journal').addEventListener('click', () => this.journal());
    this.canvas.addEventListener('webglcontextlost', e => {
      e.preventDefault();
      this.pause(true);
      $('world-pause-title').textContent = 'The 3D view stopped';
      $('world-pause-text').textContent = 'Reload the page to show it again. The server keeps your game.';
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
    this.points = []; this.actors = [];
    this.menuKey = '';
  }

  buildWorld(view, environment) {
    if (this.terrain) {
      const current = this.group;
      this.group = this.terrain;
      this.clearRoom();
      this.scene.remove(this.terrain);
      this.group = current;
    }
    this.terrain = new THREE.Group();
    this.scene.add(this.terrain);
    this.theme = themeFor({ ...view, environment });
    const theme = this.theme, terrain = this.terrain;
    this.scene.background = new THREE.Color(theme.sky);
    this.scene.fog = new THREE.Fog(theme.sky, 120, 330);
    const ground = this.material(theme.ground), stone = this.material(theme.stone);
    const pathMaterial = this.material(theme.nature ? 0x9d9574 : 0xdfc594);
    this.box(700, 1, 700, ground, 0, -0.53, 0, terrain);
    // Low hills frame a large continuous landscape, never an enclosing room.
    for (let i=0;i<28;i++) {
      const a=i*2.39996, r=150+(i%4)*22;
      const hill=this.mesh(new THREE.DodecahedronGeometry(17+i%5*3,1),ground,
        Math.sin(a)*r, -9,Math.cos(a)*r,terrain);
      hill.scale.set(1.7,0.65,1.3);
    }
    // Rivers are shallow visual water. Trails crossing them form continuous causeways.
    for (const p of environment.props.filter(p => p.kind === 'river')) this.buildScenery(p, terrain, stone);
    for (const path of environment.paths) {
      const a=environment.places.find(p=>p.id===path.fromPlace), b=environment.places.find(p=>p.id===path.toPlace);
      const trail=this.box(4,0.06,Math.hypot(b.x-a.x,b.z-a.z),pathMaterial,(a.x+b.x)/2,0.02,(a.z+b.z)/2,terrain);
      trail.rotation.y=Math.atan2(b.x-a.x,b.z-a.z);
    }
    for (const place of environment.places) {
      this.box(19,0.04,19,pathMaterial,place.x,0.015,place.z,terrain);
      if (place.kind === 'harbour') {
        const wood=this.material(0x866145);
        this.box(6,0.22,14,wood,place.x,0.12,place.z+13,terrain);
        for (const side of [-1,1]) for(let i=0;i<4;i++)
          this.box(0.2,1.4,0.2,wood,place.x+side*3,0.5,place.z+7+i*4,terrain);
      }
    }
    const scenery=sceneryFor(environment);
    for (const p of scenery.filter(p=>p.kind!=='river')) this.buildScenery(p,terrain,stone);
    this.obstacles=scenery.filter(p=>p.kind!=='river').map(p=>({x:p.x,z:p.z,radius:propRadius(p)}));
    this.root.dataset.placeCount=String(environment.places.length);
    this.root.dataset.worldBuilds=String(Number(this.root.dataset.worldBuilds||0)+1);
    this.renderer.shadowMap.needsUpdate=true;
  }

  buildScenery(p, parent, stone) {
    const group=new THREE.Group();
    group.position.set(p.x,0,p.z);
    group.rotation.y=p.heading*Math.PI/180;
    group.scale.setScalar(p.scale/100);
    parent.add(group);
    const wood=this.material(0x78553c), leaves=this.material(this.theme.nature?0x375e43:0x6c8451);
    if(p.kind==='pyramid') {
      const pyramid=this.mesh(new THREE.ConeGeometry(12,15,4),stone,0,7.5,0,group);
      pyramid.rotation.y=Math.PI/4;
    } else if(p.kind==='river') {
      // Scale only the river's width and length. Its fixed heights keep the water below trails
      // and place pads; a scaled height put the water top level with the pads, and they flickered.
      group.scale.y=1;
      const water=this.material(0x387e92,{metalness:0.35,roughness:0.28});
      this.box(9,0.025,190,water,0,0.005,0,group);
      for(let i=0;i<15;i++) {
        const ripple=this.box(4+(i%3),0.015,0.06,this.material(0x8ebbbd),Math.sin(i)*1.2,0.024,-90+i*13,group);
        ripple.rotation.y=0.08*Math.sin(i);
      }
    } else if(p.kind==='tree'||p.kind==='palm') {
      this.mesh(new THREE.CylinderGeometry(0.18,0.4,5,7),wood,0,2.5,0,group);
      if(p.kind==='tree') {
        for(let i=0;i<3;i++) this.mesh(new THREE.ConeGeometry(2.6-i*0.6,4,7),leaves,0,4+i*1.4,0,group);
      } else for(let i=0;i<7;i++) {
        const frond=this.mesh(new THREE.ConeGeometry(0.5,3.5,5),leaves,0,5.2,0,group);
        frond.rotation.set(1.15,i*Math.PI*2/7,0);
      }
    } else if(p.kind==='house') {
      this.box(6,4.5,5,stone,0,2.25,0,group);
      this.box(6.4,0.35,5.4,stone,0,4.6,0,group);
      this.box(1.1,2.3,0.05,wood,0,1.15,2.53,group);
      for(const side of [-1,1]) this.box(0.9,1.1,0.06,this.material(0x304b54),side*1.9,2.8,2.54,group);
      if(this.theme.nature) {
        const roof=this.mesh(new THREE.ConeGeometry(5,2.5,4),wood,0,5.9,0,group);
        roof.rotation.y=Math.PI/4;
      }
    } else if(p.kind==='tent') {
      const cloth=this.material(this.theme.nature?0x879569:0xe7d1a2,{side:THREE.DoubleSide});
      const roof=this.mesh(new THREE.ConeGeometry(3.6,3.6,4,1,true),cloth,0,1.8,0,group);
      roof.rotation.y=Math.PI/4;
      this.box(0.14,3.8,0.14,wood,0,1.9,0,group);
      this.box(1.1,0.7,0.8,wood,2,0.35,1,group);
    } else if(p.kind==='column') {
      this.mesh(new THREE.CylinderGeometry(0.65,0.8,6,10),stone,0,3,0,group);
      this.box(2.4,0.5,2.4,stone,0,6,0,group);
      this.box(2,0.3,2,stone,0,0.15,0,group);
    } else if(p.kind==='boat') {
      this.box(2,0.5,5,wood,0,0.3,0,group);
      for(const side of [-1,1]) this.box(0.2,0.7,5,wood,side,0.7,0,group);
      this.box(0.15,4,0.15,wood,0,2.2,0,group);
      this.mesh(new THREE.PlaneGeometry(2.4,2.8),this.material(0xe9d9b6,{side:THREE.DoubleSide}),1.1,2.7,0,group);
    } else {
      const rock=this.mesh(new THREE.DodecahedronGeometry(2.4,0),stone,0,1.1,0,group);
      rock.scale.set(1,0.8,0.85);
    }
  }

  buildRoom(view, layout) {
    this.buildStarted=performance.now();
    this.clearRoom();
    const stone=this.material(this.theme.stone);
    const brass=this.material(this.theme.glow,{metalness:0.6,roughness:0.3});
    // Each point is drawn once: a character, an object, or the shared marker of the Scene.
    for(const point of layout.points) this.buildPoint(point,layout.facing,stone,brass);
    // An objective pennant is a visual guide. It has no interaction of its own.
    const pole=this.box(0.12,8,0.12,stone,layout.place.x+8,4,layout.place.z);
    const flag=this.mesh(new THREE.PlaneGeometry(2.5,1.2),this.material(this.theme.glow,{side:THREE.DoubleSide}),
      pole.position.x+1.25,7.2,pole.position.z);
    flag.castShadow=false;
    this.root.dataset.portalCount=String(this.portals.length);
    this.root.dataset.pointCount=String(layout.points.length);
    this.root.dataset.npcCount=String(this.actors.length);
    this.renderer.shadowMap.needsUpdate=true;
    this.root.dataset.buildMs=(performance.now()-this.buildStarted).toFixed(2);
    this.awaitingFirstFrame=true;
  }

  drawMap() {
    const canvas=$('world-minimap'), ctx=canvas.getContext('2d'), e=this.environment;
    const scale=canvas.width/240, coord=n=>(n+120)*scale;
    ctx.clearRect(0,0,canvas.width,canvas.height);
    ctx.fillStyle='#162b34e8';ctx.fillRect(0,0,canvas.width,canvas.height);
    ctx.strokeStyle='#a8aa8d';ctx.lineWidth=1;
    for(const p of e.paths) {
      const a=e.places.find(q=>q.id===p.fromPlace),b=e.places.find(q=>q.id===p.toPlace);
      ctx.beginPath();ctx.moveTo(coord(a.x),coord(a.z));ctx.lineTo(coord(b.x),coord(b.z));ctx.stroke();
    }
    for(const [index,p] of e.places.entries()) {
      ctx.fillStyle=p.id===this.layout.place.id?'#ffd491':'#a5b5b5';
      ctx.beginPath();ctx.arc(coord(p.x),coord(p.z),p.id===this.layout.place.id?4:2.5,0,Math.PI*2);ctx.fill();
      ctx.font='bold 11px sans-serif'; ctx.textAlign='left';
      ctx.fillText(String(index+1),coord(p.x)+5,coord(p.z)-4);
    }
    ctx.save();ctx.translate(coord(this.position.x),coord(this.position.z));ctx.rotate(-this.yaw);
    ctx.fillStyle='#fff';ctx.beginPath();ctx.moveTo(0,-6);ctx.lineTo(-3.5,4);ctx.lineTo(3.5,4);ctx.closePath();ctx.fill();ctx.restore();
    const p=this.layout.place, distance=Math.hypot(p.x-this.position.x,p.z-this.position.z);
    const angle=Math.atan2(p.x-this.position.x,-(p.z-this.position.z))+this.yaw;
    const arrow=['↑','↗','→','↘','↓','↙','←','↖'][(Math.round(angle/(Math.PI/4))+8)%8];
    $('world-objective').textContent=this.travel?'Travelling to '+p.name
      :distance<10?'Explore '+p.name:arrow+' '+p.name+' · '+Math.round(distance)+' m';
    const legend=e.places.map((place,i)=>(i+1)+': '+place.name).join('; ');
    canvas.title=legend;
    canvas.setAttribute('aria-label','World map. '+legend+'. Your objective: '+p.name+'. '+Math.round(distance)+' metres away.');
    this.root.dataset.placeId=String(p.id);
  }

  /** Draw one point: a character, an object, or the shared marker. It faces the Player. Points with
   * actions get a ring on the ground. A click on any of its meshes selects the point. */
  buildPoint(point, facing, stone, brass) {
    const group = new THREE.Group();
    group.position.set(point.x, 0, point.z);
    group.rotation.y = facing;
    group.userData.pointId = point.id;
    this.group.add(group);
    let label = null;
    if (point.kind === 'figure') {
      const actor = this.buildActor(point.figure, group);
      actor.pointId = point.id;
      if (point.actions.length) {
        actor.label.classList.add('has-actions');
        const hint = document.createElement('span');
        hint.className = 'label-hint';
        hint.textContent = choiceCount(point.actions.length);
        actor.label.append(hint);
      }
    } else {
      this.buildObject(point.kind === 'marker' ? 'marker' : point.visual.type, group, stone, brass);
      label = document.createElement('div');
      label.className = 'portal-label';
      label.dataset.point = point.id;
      label.dataset.object = point.kind === 'marker' ? 'marker' : point.visual.type;
      const kind = document.createElement('span');
      kind.className = 'portal-number';
      kind.textContent = point.kind === 'marker' ? choiceCount(point.actions.length) : point.visual.type;
      const title = document.createElement('span');
      // A marker with one Choice shows that Choice, so the Player can read it from afar.
      title.textContent = point.kind === 'marker' && point.actions.length === 1 ? point.actions[0].label : point.title;
      label.append(kind, title);
      this.labels.appendChild(label);
    }
    let ring = null;
    if (point.actions.length) {
      ring = this.mesh(new THREE.RingGeometry(0.95, 1.0, 48),
        new THREE.MeshBasicMaterial({ color: this.theme.glow, side: THREE.DoubleSide, transparent: true, opacity: 0.65 }), 0, 0.065, 0, group);
      ring.rotation.x = -Math.PI / 2;
      ring.castShadow = false;
    }
    this.points.push({ ...point, group, label, ring });
  }

  /** Draw an object for a Choice, or the shared marker, in `group`. */
  buildObject(type, group, stone, brass) {
    const wood = this.material(0x785135), paleWood = this.material(0xb68855);
    const metal = this.material(0xc0ccd0, { metalness: 0.7, roughness: 0.3 });
    if (type === 'marker') {
      // A low stone with a glowing stone on top. It holds the Choices that have no object.
      this.mesh(new THREE.CylinderGeometry(0.45, 0.6, 1.0, 8), stone, 0, 0.5, 0, group);
      const glow = this.material(this.theme.glow, { emissive: this.theme.glow, emissiveIntensity: 0.8 });
      this.mesh(new THREE.OctahedronGeometry(0.32, 0), glow, 0, 1.35, 0, group);
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
    } else if (type === 'table') {
      this.box(2, 0.15, 1.3, wood, 0, 1.15, 0, group);
      for(const x of [-0.8,0.8]) for(const z of [-0.45,0.45]) this.box(0.12,1.1,0.12,wood,x,0.55,z,group);
      const paper=this.material(0xeee2bd);
      this.box(1.3,0.025,0.85,paper,0,1.24,0,group);
      for(let i=0;i<4;i++) this.box(0.8-i*0.1,0.008,0.02,brass,0,1.26,-0.25+i*0.15,group);
      this.mesh(new THREE.CylinderGeometry(0.14,0.14,0.2,8),metal,0.75,1.32,0,group);
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
      // Any other look gets the marker shape.
      this.buildObject('marker', group, stone, brass);
    }
  }

  /** Draw one character in `parent`, at its centre, with a name label. Returns its actor entry. */
  buildActor(foe, parent) {
    const actor = new THREE.Group();
    parent.add(actor);
    const index = foe.index;
    const body = this.material(foe.combat ? 0x70473b : index % 2 ? 0x526c77 : 0x777850);
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
      for (const side of [-1, 1]) this.box(0.05, 0.05, 0.03, this.material(0x283039), side * 0.1, 1.94, 0.26, actor);
      for (const side of [-1, 1]) {
        this.box(0.22, 0.6, 0.24, body, side * 0.2, 0.35, 0, actor);
        this.box(0.18, 0.65, 0.2, body, side * 0.43, 1.1, 0, actor);
        this.mesh(new THREE.IcosahedronGeometry(0.12), skin, side * 0.43, 0.74, 0, actor);
      }
      if (foe.combat) {
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
    const entry = { mesh: actor, alive: foe.alive, index, combat: foe.combat, label, name: foe.name };
    this.actors.push(entry);
    return entry;
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

  /** Show the view from the server. A poll with the same view does not move the camera. */
  update(view, ready) {
    this.view = view;
    this.active = view.phase !== 'title';
    this.root.hidden = !this.active;
    if (!this.active) {
      this.keys.clear(); this.touches.clear();
      this.cancelTravel(); this.travelSceneKey = '';
      this.roomKey = '';
      this.pending = false;
      this.pause(false);
      return;
    }
    this.ready = ready;
    const portals = portalsForView(view);
    this.portals = portals;
    this.combatActions(view, portals);
    const worldKey = JSON.stringify([view.seed, view.adventure, view.world, view.environment]);
    const newWorld = this.worldKey !== worldKey;
    const visits = view.reports.filter(r => r && typeof r === 'object' && r.scene).length;
    const sceneKey = JSON.stringify([worldKey, view.scene?.id, visits]);
    // The saved position belongs to one visit of one Scene.
    const sceneTag = String(view.scene?.id) + ':' + visits;
    if (newWorld) {
      this.cancelTravel();
      this.worldKey = worldKey;
      this.environment = environmentFor(view);
      const worldStarted=performance.now();
      this.buildWorld(view, this.environment);
      this.root.dataset.environmentBuildMs=(performance.now()-worldStarted).toFixed(2);
      this.environmentFrameStarted=worldStarted;
      // A live change of the same game builds the world again. The camera stays where it is.
      const gameKey = JSON.stringify([view.seed, view.adventure]);
      const sameGame = this.gameKey === gameKey;
      this.gameKey = gameKey;
      if (!sameGame) this.placeAtStart(view, sceneKey, sceneTag);
    }
    this.sceneTag = sceneTag;
    // Labels and NPCs can change without changing the command keys. Refresh them too.
    const roomKey = JSON.stringify([sceneKey, view.phase, portals,
      figuresForView(view).map(f => [f.name, f.index, f.species, f.combat])]);
    if (roomKey !== this.roomKey) {
      this.roomKey = roomKey;
      const place = placeForScene(this.environment, view.scene?.id);
      const fight = view.phase === 'fight';
      // The foes stand in front of the way the Player looks when the Fight starts.
      if (fight && (newWorld || this.previousPhase !== 'fight')) {
        this.combatAnchor = { ...this.position };
        this.combatFacing = this.yaw;
      }
      this.layout = worldLayout(interactionPoints(view, portals), place, fight ? this.combatAnchor : null,
        eventAnchorForScene(this.environment, view.scene?.id), fight ? this.combatFacing : 0);
      this.pointObstacles = this.layout.points.map(p => ({ x: p.x, z: p.z, radius: pointRadius(p) }));
      this.selectedId = null;
      this.buildRoom(view, this.layout);
      // The next scene's presentation changes; the landscape remains in place.
      this.keys.clear(); this.touches.clear();
      this.resize();
    } else if (view.fight) {
      this.actors.filter(a => a.combat).forEach(a => {
        a.alive = !!view.fight.foes[a.index]?.alive;
        a.mesh.rotation.z = a.alive ? 0 : Math.PI / 2;
        a.mesh.position.y = a.alive ? 0 : 0.3;
        a.label.textContent = a.name + ' · ' + Math.max(0, view.fight.foes[a.index]?.hp || 0) + ' HP';
      });
    }
    this.previousPhase=view.phase;
    if (!['scene', 'ended'].includes(view.phase)) {
      this.cancelTravel(); this.travelSceneKey = '';
    } else if (sceneKey !== this.travelSceneKey) {
      this.cancelTravel();
      // Wait for authoritative report playback to finish. If the Choice has a result to read, the
      // Player starts the trip with Continue. A plain Choice starts the trip at once.
      if (ready) {
        this.travelSceneKey = sceneKey;
        if (hasResultToRead(view.reports)) this.waitForContinue(); else this.startTravel();
      }
    }
    $('world-location').textContent = view.scene?.title || view.adventure;
    if (view.phase === 'fight') this.setStory('Choose a Maneuver below, or press its number. The dice decide each attack, Dodge, and hit.', false);
    else this.setStory(view.scene?.text || '', true);
    $('world-mode').textContent = view.phase === 'fight' ? 'Combat · round ' + view.fight.round
      : view.phase === 'dead' ? 'The Adventure is over' : view.phase === 'ended' ? 'The End' : 'Explore · ' + portals.length + (portals.length === 1 ? ' Choice' : ' Choices');
    $('world-hp').textContent = view.character.name + ' · ' + Math.max(0, view.character.hp) + ' / ' + view.character.maxHP + ' HP';
    $('world-loading').hidden = ready;
    this.root.dataset.phase = view.phase;
    this.root.dataset.sceneId = String(view.scene?.id ?? '');
    this.root.dataset.ready = String(ready && !this.pending);
    const ended = ['ended', 'dead'].includes(view.phase) || view.inputs.length === 0;
    document.body.classList.toggle('game-ended', ended);
  }

  /** Show `text` under the Scene title. With `unfold`, new text appears word by word, like a story
   * being told. It starts when the dice and the transition end. The same text again changes
   * nothing. A click on the text shows all of it. Every word is in the page from the start, so a
   * screen reader reads the whole text. */
  setStory(text, unfold) {
    if (text === this.story?.text) return;
    const box = $('world-description');
    if (!unfold || this.reducedMotion?.matches || !box.replaceChildren) {
      box.textContent = text;
      this.story = { text, words: [], next: 0 };
      return;
    }
    box.replaceChildren();
    const words = [];
    for (const part of storyTimeline(text)) {
      if (part.space) { box.append(part.space); continue; }
      const span = document.createElement('span');
      span.className = 'story-word';
      span.textContent = part.word;
      box.append(span);
      words.push({ span, at: part.at });
    }
    box.scrollTop = 0;
    this.story = { text, words, next: 0, start: null };
  }

  /** Show the words of the story whose time has come. Called once per frame. */
  unfoldStory() {
    const story = this.story;
    if (!story || story.next >= story.words.length) return;
    if (story.start === null) {
      if (!this.ready || this.travel || this.waiting) return;
      story.start = performance.now();
    }
    const now = performance.now() - story.start;
    let last = null;
    while (story.next < story.words.length && story.words[story.next].at <= now) {
      last = story.words[story.next++].span;
      last.classList.add('shown');
    }
    // Keep the newest word in sight when the text is longer than its box.
    const box = $('world-description');
    if (last && last.offsetTop + last.offsetHeight > box.scrollTop + box.clientHeight) {
      box.scrollTop = last.offsetTop + last.offsetHeight - box.clientHeight;
    }
  }

  /** Show the rest of the story at once. */
  finishStory() {
    const story = this.story;
    if (!story) return;
    for (; story.next < story.words.length; story.next++) story.words[story.next].span.classList.add('shown');
  }

  /** Put the Player at the start of a new game: at the arrival point of its Scene, with no
   * transition. After a reload, the saved position and angle of the same Scene come back. */
  placeAtStart(view, sceneKey, sceneTag) {
    const place = placeForScene(this.environment, view.scene?.id);
    this.position = arrivalForLayout(worldLayout([], place, null, eventAnchorForScene(this.environment, view.scene?.id)));
    this.yaw = 0; this.pitch = DEFAULT_PITCH;
    this.travelSceneKey = sceneKey;
    this.storageKey = 'rpg-position:' + view.adventure + ':' + view.seed;
    try {
      const saved = JSON.parse(localStorage.getItem(this.storageKey));
      if (saved && saved.scene === sceneTag && Number.isFinite(saved.x) && Number.isFinite(saved.z)
        && Math.abs(saved.x)<115 && Math.abs(saved.z)<115
        && this.obstacles.every(o=>Math.hypot(saved.x-o.x,saved.z-o.z)>o.radius+0.4)) {
        this.position = {x:saved.x,z:saved.z};
        this.yaw = Number.isFinite(saved.yaw) ? saved.yaw : 0;
      }
    } catch { /* Storage is optional. */ }
  }

  /** The closest point with Choices in reach of the Player, or null. */
  nearest() {
    return nearestPoint(this.position, this.layout?.points || []);
  }

  /** The point whose menu shows now: the one in reach, else the one the Player clicked. */
  menuPoint() {
    if (this.travel || this.waiting || this.view?.phase !== 'scene') return null;
    const near = this.nearest();
    if (near) return near;
    const selected = this.layout?.points.find(p => p.id === this.selectedId && p.actions.length);
    if (selected && Math.hypot(this.position.x - selected.x, this.position.z - selected.z) < 30) return selected;
    return null;
  }

  /** E picks the Choice of the point in the menu, when it has only one. */
  useNearest() {
    const p = this.menuPoint();
    if (p && p.actions.length === 1) this.choose(p.actions[0]);
  }

  /** Select the person or object under the pointer, so its menu shows. A click on nothing clears it. */
  selectAt(clientX, clientY) {
    if (!this.canMove()) return;
    const rect = this.canvas.getBoundingClientRect();
    const pointer = new THREE.Vector2(((clientX - rect.left) / rect.width) * 2 - 1, -((clientY - rect.top) / rect.height) * 2 + 1);
    this.raycaster.setFromCamera(pointer, this.camera);
    this.selectedId = null;
    for (const hit of this.raycaster.intersectObjects(this.group.children, true)) {
      let obj = hit.object;
      while (obj && obj.userData.pointId === undefined) obj = obj.parent;
      const point = obj && this.layout.points.find(p => p.id === obj.userData.pointId);
      if (point) {
        if (point.actions.length) this.selectedId = point.id;
        return;
      }
    }
  }

  /** Draw the menu of the point in reach or clicked: one button for each of its Choices. */
  renderMenu(canMove) {
    const point = this.menuPoint();
    $('world-prompt').hidden = !point;
    const key = point ? JSON.stringify([point.id, point.actions.map(a => [a.key, a.label])]) : '';
    if (key !== this.menuKey) {
      this.menuKey = key;
      const list = $('world-menu');
      list.replaceChildren();
      if (point) {
        $('world-choice').textContent = point.kind === 'object'
          ? point.visual.type[0].toUpperCase() + point.visual.type.slice(1) : point.title;
        $('world-detail').textContent = point.actions.length === 1
          ? 'Click the Choice, or press E or 1.' : 'Click a Choice, or press its number.';
        point.actions.forEach((action, i) => {
          const button = document.createElement('button');
          button.type = 'button';
          button.dataset.inputKey = action.key;
          const number = document.createElement('span');
          number.className = 'menu-number';
          number.textContent = String(i + 1);
          button.append(number, document.createTextNode(action.label));
          button.addEventListener('click', () => this.choose(action));
          list.appendChild(button);
        });
      }
    }
    for (const button of $('world-menu').children) button.disabled = !canMove;
    return point;
  }

  canMove() {
    return this.active && this.ready && !this.pending && !this.paused && !this.travel && !this.waiting
      && !document.body.classList.contains('journal-open') && !document.querySelector('dialog[open]');
  }

  /** After a Choice with a result (a roll, the end of a Fight) leads to a new Scene, hold the result
   * on screen. The trip to the new Scene starts only when the Player presses Continue. */
  waitForContinue() {
    this.waiting = true;
    this.keys.clear(); this.touches.clear();
    this.selectedId = null;
    $('world-continue').hidden = false;
    $('world-continue-button').textContent = 'Continue to ' + this.layout.place.name;
  }

  /** Start the trip to the new Scene, if it waits for Continue. It never sends an input. */
  continueOn() {
    if (!this.waiting || this.paused) return;
    this.waiting = false;
    $('world-continue').hidden = true;
    $('world-events').hidden = true;
    this.startTravel();
  }

  /** Move the camera to the next Scene with a short glide or fade. The Player cannot move or
   * choose until it ends. It never sends an input. */
  startTravel() {
    const arrival = arrivalForLayout(this.layout);
    const plan = planTransition(this.position, arrival, this.yaw, this.pitch, this.layout.facing);
    this.keys.clear(); this.touches.clear();
    this.selectedId = null;
    this.travel = { plan, t: 0 };
    if (this.reducedMotion.matches) { this.finishTravel(); return; }
    this.root.dataset.travelling = 'true';
    this.root.dataset.transition = plan.kind;
    const overlay = $('world-travel');
    overlay.hidden = plan.kind !== 'fade';
    overlay.style.opacity = '0';
    $('world-travel-status').textContent = this.layout.place.name;
  }

  cancelTravel() {
    this.travel = null;
    this.waiting = false;
    $('world-continue').hidden = true;
    this.root.dataset.travelling = 'false';
    const overlay = $('world-travel');
    overlay.hidden = true;
    if (overlay.style) overlay.style.opacity = '0';
  }

  /** End the transition at its last frame, so the camera does not jump. */
  finishTravel() {
    if (!this.travel) return;
    const end = transitionAt(this.travel.plan, this.travel.plan.duration);
    this.position = end.position;
    this.yaw = end.yaw; this.pitch = end.pitch;
    this.cancelTravel();
    this.keys.clear(); this.touches.clear();
    this.savePosition();
  }

  savePosition() {
    try { localStorage.setItem(this.storageKey, JSON.stringify({ ...this.position, yaw: this.yaw, scene: this.sceneTag })); }
    catch { /* Storage is optional. */ }
  }

  travelFrame(dt) {
    this.travel.t += dt;
    const now = transitionAt(this.travel.plan, this.travel.t);
    this.position = now.position;
    this.yaw = now.yaw; this.pitch = now.pitch;
    $('world-travel').style.opacity = String(now.fade);
    if (now.done) this.finishTravel();
  }

  move(dx, dz) {
    if (!this.canMove() || !this.layout) return;
    // People and objects are solid, so the Player stops in front of them.
    this.position = moveInWorld(this.position, dx, dz, [...this.obstacles, ...(this.pointObstacles || [])], this.layout.bound);
  }

  nudge(direction) {
    const forward = Number(direction === 'arrowup') - Number(direction === 'arrowdown');
    const right = Number(direction === 'arrowright') - Number(direction === 'arrowleft');
    this.move((-Math.sin(this.yaw) * forward + Math.cos(this.yaw) * right) * 0.55,
      (-Math.cos(this.yaw) * forward - Math.sin(this.yaw) * right) * 0.55);
  }

  async choose(portal) {
    if (!this.ready || this.paused || this.pending || !this.active || this.travel) return;
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

  /** Put a label at the screen position of a world point, or hide it when it is off screen or far. */
  placeLabel(label, world, maxDistance = 22) {
    const point = world.clone().project(this.camera);
    const hidden = world.distanceTo(this.camera.position) > maxDistance || point.z < -1 || point.z > 1
      || Math.abs(point.x) > 1.1 || Math.abs(point.y) > 1.2;
    label.hidden = hidden;
    if (!hidden) {
      label.style.left = ((point.x + 1) * 50) + '%';
      label.style.top = ((1 - point.y) * 50) + '%';
    }
  }

  frame(time) {
    const dt = this.frameTime ? Math.min((time - this.frameTime) / 1000, 0.05) : 0;
    this.frameTime = time;
    if (!this.active || document.hidden || !this.layout) return;
    this.elapsed += dt;
    let moving = false;
    if (this.travel && !this.paused) this.travelFrame(dt);
    const canMove = this.canMove();
    if (canMove) {
      const has = (...keys) => keys.some(k => this.keys.has(k) || [...this.touches.values()].includes(k));
      let forward = Number(has('w', 'z', 'arrowup')) - Number(has('s', 'arrowdown'));
      let right = Number(has('d', 'arrowright')) - Number(has('a', 'q', 'arrowleft'));
      const length = Math.hypot(forward, right);
      moving = length > 0;
      if (moving) {
        forward /= length; right /= length;
        const speed = has('shift') ? 11 : 5;
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
    const menu = this.renderMenu(canMove);
    this.unfoldStory();
    for (const point of this.points) {
      if (point.ring) point.ring.material.opacity = menu?.id === point.id ? 1 : 0.55;
      if (!point.label) continue;
      this.placeLabel(point.label, new THREE.Vector3(point.x, 2.3, point.z));
      // The open menu shows the same words, so its label hides. Close up, it would cover the text.
      if (menu?.id === point.id) point.label.hidden = true;
    }
    for (const actor of this.actors) {
      const age = this.effect ? this.elapsed - this.effect.started : 10;
      const pulse = age < 0.6 && !reduced ? Math.sin(Math.PI * Math.min(1, age / 0.6)) : 0;
      const attacking = this.effect?.kind === 'attack' && this.effect.data.attacker === actor.index;
      const hurt = this.effect?.kind === 'damage' && this.effect.data.injury > 0 && this.effect.data.defender === actor.index;
      // The actor sits at the centre of its point. A lunge moves it toward the Player.
      actor.mesh.position.z = attacking ? pulse * 0.75 : 0;
      actor.mesh.position.x = hurt ? Math.sin(age * 45) * pulse * 0.09 : 0;
      if (actor.alive) actor.mesh.position.y = reduced ? 0 : Math.sin(this.elapsed * 2 + actor.index) * 0.03;
      actor.label.classList.toggle('taking-hit', !!hurt && pulse > 0);
      actor.label.classList.toggle('near', !!menu && menu.id === actor.pointId);
      this.placeLabel(actor.label, actor.mesh.localToWorld(new THREE.Vector3(0, 2.35, 0)));
    }
    // Presentation coordinates let navigation tests observe movement without controlling it.
    this.root.dataset.playerX = this.position.x.toFixed(3);
    this.root.dataset.playerZ = this.position.z.toFixed(3);
    this.root.dataset.yaw = this.yaw.toFixed(3);
    this.root.dataset.menu = menu ? menu.id : '';
    if (!this.lastMapFrame || time-this.lastMapFrame>100) {
      this.drawMap(); this.lastMapFrame=time;
    }
    // Save the position while the Player walks, and once more when the walk stops.
    if((moving && (!this.lastSavedPosition || time-this.lastSavedPosition>500)) || (!moving && this.wasMoving)) {
      this.savePosition();
      this.lastSavedPosition=time;
    }
    this.wasMoving=moving;
    this.renderer.render(this.scene, this.camera);
    if (this.environmentFrameStarted !== undefined) {
      this.root.dataset.environmentFirstFrameMs=(performance.now()-this.environmentFrameStarted).toFixed(2);
      this.environmentFrameStarted=undefined;
    }
    if (this.awaitingFirstFrame) {
      this.root.dataset.firstFrameMs = (performance.now() - this.buildStarted).toFixed(2);
      this.awaitingFirstFrame = false;
    }
  }
}
