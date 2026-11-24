const $ = (s) => document.querySelector(s);
const $$ = (s) => [...document.querySelectorAll(s)];
const NS = 'http://www.w3.org/2000/svg';
let job = null, difficulty = 'easy', tab = 'scenes', selected = null, combatData = null;
let camera = {x:0,y:0,k:1}, worldSize = {w:1000,h:500}, drag = null, generationStarted = 0;
let requestBusy = false, pollTimer = null, serverReady = false;
let restoringJob = false, combatRequest = 0, combatNodeId = null, nodePositions = new Map();
function el(tag, attrs = {}, text = '') { const n=document.createElement(tag);Object.entries(attrs).forEach(([k,v])=>n.setAttribute(k,v));if(text)n.textContent=text;return n; }
function svg(tag, attrs={}, text='') {const n=document.createElementNS(NS,tag);Object.entries(attrs).forEach(([k,v])=>n.setAttribute(k,v));if(text)n.textContent=text;return n;}
function pct(v){return (v*100).toFixed(1)+'%';}
function error(message){$('#error').textContent=message;$('#error').hidden=!message;}
async function api(path, body){const r=await fetch(path,body?{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body)}:{});const d=await r.json();if(!r.ok)throw Error(d.error||'Request failed');return d;}
$$('#difficulty button').forEach(b=>b.onclick=()=>{difficulty=b.dataset.value;$$('#difficulty button').forEach(x=>x.classList.toggle('active',x===b));$('#target').textContent={easy:'50%',medium:'70%',hard:'90%'}[difficulty];});
$('#branches').oninput=()=>{
  const routes=Number($('#branches').value), minimum=19+routes;
  $('#branches-label').textContent=routes;$('#max-nodes').min=minimum;
  $('#node-help').textContent=`${minimum}–60 nodes. Includes HP variants and Win/Lose. Internal combat states are separate.`;
  if(Number($('#max-nodes').value)<minimum)$('#max-nodes').value=minimum;
};
$('#generate-form').onsubmit=async e=>{
  e.preventDefault();if(requestBusy||!serverReady)return;error('');requestBusy=true;$('#generate').disabled=true;
  clearTimeout(pollTimer);generationStarted=Date.now();combatData=null;selected=null;tab='scenes';
  combatRequest++;combatNodeId=null;$('#combat-browser').hidden=true;$('#combat-context').hidden=true;$('#combat-tab').disabled=true;
  $('#graph').toggleAttribute('hidden',true);$('#proof-panel').hidden=true;$('#legend').hidden=true;$('#empty').hidden=false;$('#character-panel').hidden=true;
  try{job=await api('/api/generate',{difficulty,branches:Number($('#branches').value),max_nodes:Number($('#max-nodes').value),character_count:Number($('#character-count').value)});rememberJob();renderStatus();poll();}
  catch(e){error(e.message);requestBusy=false;$('#generate').disabled=false;}
};
async function poll(){try{const previous=job.document?.model_hash;job=await api('/api/jobs/'+job.id);renderStatus();if(job.document&&job.document.model_hash!==previous){if(restoringJob){restoreSettings();restoringJob=false;}if(tab==='scenes'&&!job.document.scenes)tab='adventure';selected=tab==='scenes'?job.document.nodes[job.current].scene_id:job.current;renderCombatPicker();renderGraph(true);renderCurve();renderCharacters();renderInspector();if(job.fight!=null)await viewCombat(job.fight,job.current);}renderProofs();if(['generating','verifying'].includes(job.status)||rulePending())pollTimer=setTimeout(poll,1000);else{requestBusy=false;$('#generate').disabled=false;renderInspector();if(job.error)error(job.error);}}catch(e){error(e.message);requestBusy=false;$('#generate').disabled=false;}}
function renderStatus(){
  const status=$('#status');status.className='badge '+({verified:'verified',rejected:'rejected',verifying:'pending',generating:'pending'}[job?.status]||'neutral');status.textContent={verified:'Lean verified',rejected:'Not accepted',verifying:'Checking in Lean',generating:'Generating'}[job?.status]||'Ready to generate';
  status.title=job?.stage||'';renderRules();
  if(!job?.document)return;
  const d=job.document;$('#world-title').textContent=d.title;$('#loss').textContent=pct(d.loss);$('#loss-detail').textContent=`Target ${pct(Number(d.target.split('/')[0])/Number(d.target.split('/')[1]||1))} ± 5 points`;$('#loss').title=d.exact_loss;
  $('#states').textContent=d.nodes.length;$('#states-detail').textContent=`Limit ${d.max_nodes} · ${d.character_count} characters`;$('#timing').textContent=`${job.generation_seconds?.toFixed(2)||'…'}s / ${job.verification_seconds?job.verification_seconds.toFixed(1)+'s':((Date.now()-generationStarted)/1000).toFixed(0)+'s…'}`;
  $('#timing-detail').textContent=job.stage;$('#empty').hidden=true;$('#legend').hidden=tab==='certificate';$('#combat-tab').disabled=!d.nodes.some(n=>n.combat);
  $('#combat-choice').disabled=job.fight!=null;$('#scenes-tab').disabled=!d.scenes;
  $('#uniform-step').disabled=job.status!=='verified'||rulePending()||(tab==='combat'&&job.fight==null)||(job.fight==null&&['lose','win'].includes(d.nodes[job.current].kind));$('#restart').disabled=job.status!=='verified'||rulePending();
  $('#duration-note').textContent=job.status==='verified'?`All times covered; checked from t=${d.timestamp||0}, all future event times.`:'Candidate curve; awaiting the Lean certificate.';
}
function setTab(t){if(t==='scenes'&&t!==tab)selected=job?.document?.nodes[job.current]?.scene_id;else if(tab==='scenes'&&t==='adventure')selected=job?.current;tab=t;$$('[data-tab]').forEach(b=>b.classList.toggle('active',b.dataset.tab===t));$('#combat-context').hidden=t!=='combat';$('#proof-panel').hidden=t!=='certificate';$('#graph').toggleAttribute('hidden',t==='certificate'||!job?.document);$('#legend').hidden=t==='certificate'||!job?.document;$('#empty').hidden=!!job?.document;$('.graph-tools').style.visibility=t==='certificate'?'hidden':'visible';if(t==='certificate')renderProofs();else renderGraph(true);renderInspector();}
$$('[data-tab]').forEach(b=>b.onclick=()=>b.dataset.tab==='combat'?openSelectedCombat():setTab(b.dataset.tab));
function graphNodes(){if(tab==='scenes')return (job.document.scenes||[]).map(s=>({...s,kind:'scene',hp:0}));if(tab==='combat'&&combatData)return combatData.nodes.map(n=>({...n,title:n.terminal?(n.lose?'Defeat':'Victory'):(n.turn===0?'Player’s turn':'Opponent’s turn'),hp:n.a,kind:n.terminal?(n.lose?'lose':'win'):'combat',column:2*(3-n.a)+(n.turn===0?0:1)}));return job.document.nodes;}
function renderGraph(fit=false){
  if(!job?.document||tab==='certificate')return;
  $('#graph').toggleAttribute('hidden',false);$('#proof-panel').hidden=true;$('#empty').hidden=true;$('#legend').hidden=false;
  $$('[data-tab]').forEach(b=>b.classList.toggle('active',b.dataset.tab===tab));
  const legend=$('#legend');legend.replaceChildren();for(const [color,label] of (tab==='scenes'?[['blue','Active scene']]:[['blue','Current state'],['amber','Combat'],['green','Victory'],['red','Defeat']])){const item=el('span',{},label);item.prepend(el('i',{class:color}));legend.append(item);}
  const root=$('#graph');root.setAttribute('aria-label',tab==='scenes'?'Scene graph':tab==='combat'?'Combat state graph':'Game state graph');root.replaceChildren();const rect=root.getBoundingClientRect();root.setAttribute('viewBox',`0 0 ${rect.width} ${rect.height}`);
  const defs=svg('defs');for(const [id,color] of [['arrow','#bbc7d8'],['active-arrow','#567fd0']]){const m=svg('marker',{id,markerWidth:6,markerHeight:6,refX:5,refY:3,orient:'auto'});m.append(svg('path',{d:'M0,0 L6,3 L0,6 Z',fill:color}));defs.append(m);}root.append(defs);
  const scene=svg('g',{id:'scene'});root.append(scene);const nodes=graphNodes();const edges=tab==='combat'?combatData.edges:tab==='scenes'?job.document.scene_edges:job.document.edges;const positions=new Map();const columns=new Map();
  for(const n of nodes){if(!columns.has(n.column))columns.set(n.column,[]);columns.get(n.column).push(n);}
  const maxRows=Math.max(...[...columns.values()].map(a=>a.length));const height=Math.max(300,maxRows*88+70);const step=tab==='combat'?184:190;
  const firstColumn=Math.min(...columns.keys());
  columns.forEach((group,col)=>{group.sort((a,b)=>a.hp-b.hp||a.id-b.id);group.forEach((n,i)=>positions.set(n.id,{x:30+(col-firstColumn)*step,y:40+i*88+(height-90-group.length*88)/2}));});
  if(tab==='adventure'){for(const n of nodes.filter(n=>n.kind==='lose'))positions.set(n.id,{x:30+n.column*step,y:height+24});}
  if(tab==='scenes'){[...nodes].sort((a,b)=>a.column-b.column||a.id.localeCompare(b.id)).forEach((n,i)=>{const row=Math.floor(i/3),col=row%2?2-i%3:i%3;positions.set(n.id,{x:30+col*210,y:35+row*130});});}
  nodePositions=positions;
  worldSize={w:Math.max(...[...positions.values()].map(p=>p.x))+175,h:Math.max(...[...positions.values()].map(p=>p.y))+110};
  const active=tab==='combat'?(job.fight??combatData.entry):tab==='scenes'?job.document.nodes[job.current].scene_id:job.current;
  for(const edge of edges){const a=positions.get(edge.source),b=positions.get(edge.target);if(!a||!b)continue;
    const highlighted=edge.source===active;let path;const x=a.x+153,y=a.y+30,tx=b.x,ty=b.y+30;
    if(edge.source===edge.target)path=`M${a.x+115},${a.y} C${a.x+115},${a.y-27} ${a.x+179},${a.y-27} ${a.x+179},${a.y+17} Q${a.x+179},${a.y+30} ${a.x+153},${a.y+30}`;
    else if(tab==='adventure'&&job.document.nodes[edge.target].kind==='lose'){const lane=worldSize.h-35-(edge.source%3)*7;path=`M${x},${y} C${x+24},${y} ${x+24},${lane} ${x+56},${lane} L${tx-38},${lane} Q${tx-12},${lane} ${tx},${ty}`;}
    else if(tx>x)path=`M${x},${y} C${x+Math.max(35,(tx-x)/2)},${y} ${tx-Math.max(35,(tx-x)/2)},${ty} ${tx},${ty}`;
    else path=`M${x},${y} C${x+50},${y-45} ${tx-45},${ty-45} ${tx},${ty}`;
    const p=svg('path',{d:path,fill:'none',stroke:highlighted?'#6b8ed1':'#cbd5e3','stroke-width':highlighted?1.5+(edge.value||0):1,'stroke-opacity':highlighted?1:.65,'marker-end':`url(#${highlighted?'active-arrow':'arrow'})`});p.append(svg('title',{},tab==='scenes'?`${edge.source} → ${edge.target} · ${edge.witnesses.length} event transitions`:`State ${edge.source} → ${edge.target} · ${pct(edge.value)} · Exact: ${edge.probability}`));scene.append(p);
    if(highlighted&&edge.value>.03){const text=svg('text',{x:x+22,y:y+(ty-y)*.22-7,'font-size':10,fill:'#5073af','paint-order':'stroke',stroke:'white','stroke-width':4},pct(edge.value));scene.append(text);}
  }
  for(const n of nodes){const p=positions.get(n.id),isCurrent=n.id===active,isSelected=n.id===selected;const colors={combat:['#fff0ce','#b57615'],win:['#f0f8f2','#acd1b9'],lose:['#fcf1f2','#dcb0b5'],rest:['#f4f8fc','#bacde0'],scene:['#fff','#d3dce8'],treasure:['#faf8ed','#d6cc9c']};const c=colors[n.kind]||colors.scene;
    const g=svg('g',{class:'node',transform:`translate(${p.x},${p.y})`,tabindex:0,role:'button','aria-label':tab==='scenes'?`${n.title}, ${n.events.length} events`:`${n.title}, HP ${n.hp}, state ${n.id}`});g.append(svg('rect',{width:153,height:60,rx:8,fill:isCurrent?'#eef4ff':c[0],stroke:isCurrent?'#4d7bcc':isSelected?'#90a6cc':c[1],'stroke-width':isCurrent?2:1}));
    g.append(svg('circle',{cx:13,cy:16,r:3,fill:isCurrent?'#4d7bcc':({combat:'#bd9149',win:'#56876b',lose:'#bd6c76'}[n.kind]||'#a0aec1')}));
    g.append(svg('text',{x:23,y:20,'font-size':8,'font-weight':600,'letter-spacing':.5,fill:'#8b96a5'},tab==='scenes'?`${n.events.length} EVENTS · ${n.states.length} STATES`:`${n.kind.toUpperCase()} · ${n.id}`));
    g.append(svg('text',{x:12,y:39,'font-size':11,'font-weight':550,fill:'#34465d'},n.title.length>23?n.title.slice(0,22)+'…':n.title));
    const detail=tab==='scenes'?`${n.characters.length} NPCs · ${n.objects.length} objects${isCurrent?' · ACTIVE':''}`:tab==='combat'?`HP ${n.a} / ${n.b}${n.guard?' · defense +2':''}`:`HP ${n.hp}${isCurrent?' · YOU ARE HERE':''}`;g.append(svg('text',{x:12,y:52,'font-size':8,fill:isCurrent?'#4775c2':'#8895a6'},detail));g.append(svg('title',{},n.title));
    const selectNode=()=>{selected=n.id;if(tab==='adventure'&&n.combat)$('#combat-choice').value=n.id;renderGraph(false);renderInspector();};
    g.onclick=()=>{if(drag?.moved)return;selectNode();};g.onkeydown=e=>{if(e.key==='Enter')selectNode();};scene.append(g);
  }
  $('#graph-note').textContent=tab==='scenes'?'Locations group events. Arrows are possible travel, not probability laws. Only current-event actions are playable.':tab==='combat'?'Exact internal states: both HP values, turn and defense. Edges use uniform Attack / Defend.':'Every node is an exact (event, HP) state. Edge weights include uniform choices and resolved combats.';
  if(fit)fitGraph();else applyCamera();
}
function applyCamera(){const g=$('#scene');if(g)g.setAttribute('transform',`translate(${camera.x},${camera.y}) scale(${camera.k})`);}
function fitGraph(){const r=$('#graph').getBoundingClientRect();camera.k=Math.min((r.width-35)/worldSize.w,(r.height-55)/worldSize.h,1.3);camera.x=(r.width-worldSize.w*camera.k)/2;camera.y=(r.height-worldSize.h*camera.k)/2-8;applyCamera();}
function zoom(factor,px,py){const r=$('#graph').getBoundingClientRect();const x=px??r.width/2,y=py??r.height/2;const old=camera.k;camera.k=Math.max(.15,Math.min(3.5,old*factor));camera.x=x-(x-camera.x)*camera.k/old;camera.y=y-(y-camera.y)*camera.k/old;applyCamera();}
$('#zoom-in').onclick=()=>zoom(1.25);$('#zoom-out').onclick=()=>zoom(.8);$('#fit').onclick=fitGraph;
$('#graph').addEventListener('wheel',e=>{e.preventDefault();const r=$('#graph').getBoundingClientRect();zoom(e.deltaY<0?1.1:.9,e.clientX-r.left,e.clientY-r.top);},{passive:false});
$('#graph').onpointerdown=e=>{drag={x:e.clientX,y:e.clientY,ox:camera.x,oy:camera.y,moved:false};};
window.addEventListener('pointermove',e=>{if(!drag||!e.buttons)return;const dx=e.clientX-drag.x,dy=e.clientY-drag.y;if(Math.abs(dx)+Math.abs(dy)>4)drag.moved=true;if(drag.moved){camera.x=drag.ox+dx;camera.y=drag.oy+dy;applyCamera();}});
window.addEventListener('pointerup',()=>setTimeout(()=>drag=null,0));
window.addEventListener('resize',()=>{if(job?.document)renderGraph(true);});
function button(text,fn,cls='action-card',disabled=false){const b=el('button',{type:'button',class:cls},text);b.disabled=disabled;b.onclick=fn;return b;}
function renderSceneInspector(){
  const panel=$('#inspect');panel.replaceChildren();
  const d=job.document, current=d.nodes[job.current], active=current.scene_id;
  const location=d.scenes?.find(s=>s.id===(selected??active));
  if(!location){panel.append(el('h3',{},'No active scene'),el('p',{class:'muted'},'This path has reached a terminal output. Win and Lose are not physical locations.'));}
  else {
    panel.append(el('h3',{},location.title),el('div',{class:'state-meta'},location.id===active?'ACTIVE SCENE':'SCENE INSPECTION'));
    const people=location.characters.map(id=>d.characters.find(c=>c.id===id)?.name||String(id));
    if(location.id===active)people.unshift('Player');
    panel.append(el('p',{class:'muted'},'Characters: '+(people.join(', ')||'None')));
    panel.append(el('p',{class:'muted'},'Objects: '+(location.objects.map(id=>d.scene_items.find(i=>i.id===id)?.name||String(id)).join(', ')||'None')));
    panel.append(el('p',{class:'muted'},'Presence does not unlock actions. Choices belong to the current event.'));
    panel.append(el('h4',{},`${location.events.length} events in this scene`));
    for(const event of location.events){
      const variants=d.nodes.filter(n=>n.scene===event);
      const node=variants.find(n=>n.id===job.current)||variants.find(n=>n.hp===current.hp)||variants[0];
      panel.append(button(`${node.id===job.current?'● ':''}${node.title} · ${variants.length} HP states`,()=>{setTab('adventure');selected=node.id;renderGraph(false);renderInspector();},'scene-event'));
    }
    if(location.id===active){
      panel.append(el('h4',{},`Current event: ${current.title}`),el('p',{class:'muted'},`Node ${current.id} · HP ${current.hp} · t=${job.timestamp||0}`));
      const ready=job.status==='verified'&&!rulePending();
      if(job.fight!=null)panel.append(button('Resume combat →',()=>viewCombat(job.fight,job.current),'action-card',!ready));
      else {
        if(current.combat)panel.append(button('Play this combat →',()=>act({mode:'startCombat'}),'action-card',!ready));
        for(const option of d.choices.find(c=>c.state===job.current)?.actions||[])panel.append(button(option.label+' →',()=>act({mode:'choice',action:option.label}),'action-card',!ready));
      }
    } else if(active)panel.append(button('Focus active scene',()=>{selected=active;renderGraph(false);renderSceneInspector();},'secondary'));
  }
  $('#history').replaceChildren();for(const line of [...(job.history||[])].reverse().slice(0,8))$('#history').append(el('li',{},line));
  renderStatus();
}
function renderInspector(){
  if(!job?.document)return;if(tab==='scenes'){renderSceneInspector();return;}const panel=$('#inspect');panel.replaceChildren();const ready=job.status==='verified'&&!rulePending();const active=tab==='combat'?(job.fight??combatData?.entry):job.current;const id=selected??active;const node=graphNodes().find(n=>n.id===id)||graphNodes().find(n=>n.id===active);if(!node)return;
  panel.append(el('h3',{},node.title));panel.append(el('div',{class:'state-meta'},`STATE ${node.id} · ${tab==='combat'?'INTERNAL COMBAT':node.scene.toUpperCase()}`));
  const hp=el('div',{class:'hp-meter','aria-label':`Health ${node.hp} of ${job.document.hp_max}`});for(let i=0;i<job.document.hp_max;i++)hp.append(el('i',{class:i<node.hp?'full':''}));panel.append(hp);
  if(tab!=='combat'&&node.characters){panel.append(el('p',{class:'muted'},'Characters: '+node.characters.map(id=>job.document.characters[id].name).join(', ')));}
  if(tab==='combat'){panel.append(el('p',{class:'muted'},`Player HP ${node.a} · Opponent HP ${node.b}. ${node.guard?'The waiting fighter has defense +2.':'No defense bonus is active.'}`));}
  else if(node.combat){panel.append(el('p',{class:'muted'},`Opponent HP ${node.combat.enemy_hp}. Defeat chance ${pct(Number(node.combat.lose.split('/')[0])/Number(node.combat.lose.split('/')[1]||1))}. Expected duration ${node.combat.expected_actions.toFixed(1)} internal actions.`));panel.append(button('Inspect combat graph ↗',()=>viewCombat(node.combat.entry,node.id),'small-link'));}
  if(id!==active){panel.append(button('Focus the current state',()=>{selected=active;renderInspector();},'secondary'));}
  else if(tab==='combat'&&job.fight==null){panel.append(el('p',{class:'muted'},'Inspecting this combat. Return to the game graph to enter from the current event.'));panel.append(button('Return to game graph',()=>{selected=job.current;setTab('adventure');},'secondary'));}
  else if(['win','lose'].includes(node.kind)){panel.append(el('div',{class:'state-outcome '+node.kind},node.kind==='win'?'The path reached Win.':'The path reached Lose.'));
  }else{
    const options=tab==='combat'?combatData.choices.find(c=>c.state===active)?.actions:job.document.choices.find(c=>c.state===active)?.actions;
    if(tab!=='combat'&&node.combat)panel.append(button('Play this combat →',()=>act({mode:'startCombat'}),'action-card',!ready));
    for(const option of options||[])panel.append(button(option.label+' →',()=>act({mode:'choice',action:option.label}),'action-card',!ready));
  }
  $('#history').replaceChildren();for(const line of [...(job.history||[])].reverse().slice(0,8))$('#history').append(el('li',{},line));if(!job.history?.length)$('#history').append(el('li',{},'Your path starts at the initial node.'));
  renderStatus();
}
async function viewCombat(entry,nodeId=null){
  const request=++combatRequest, jobId=job.id;
  if(job.fight!=null){entry=job.fight;nodeId=job.current;}
  const node=job.document.nodes.find(n=>n.id===nodeId&&n.combat)||job.document.nodes.find(n=>n.combat?.entry===entry);
  try{
    const data=await api(`/api/combat/${jobId}?entry=${entry}`);
    if(request!==combatRequest||job.id!==jobId)return;
    combatData=data;combatNodeId=node?.id;selected=job.fight??entry;
    if(node)$('#combat-choice').value=node.id;
    $('#combat-context').textContent=`${node?.title||'Combat'} · Player HP ${node?.hp??data.nodes.find(n=>n.id===entry)?.a} · Opponent HP ${node?.combat.enemy_hp??'—'} · ${data.nodes.length} reachable internal states · ${job.fight!=null?'Playing':'Inspection only — game position unchanged'}`;
    setTab('combat');
  }catch(e){if(request===combatRequest)error(e.message);}
}
async function act(body){if(requestBusy)return;requestBusy=true;error('');try{const previousTab=tab;job=await api('/api/action',{id:job.id,revision:job.revision,...body});if(job.fight!=null){if(combatData&&tab==='combat'&&combatNodeId===job.current&&combatData.nodes.some(n=>n.id===job.fight)){selected=job.fight;renderGraph(false);renderInspector();}else await viewCombat(job.fight,job.current);}else{tab=previousTab==='scenes'?'scenes':'adventure';selected=tab==='scenes'?job.document.nodes[job.current].scene_id:job.current;$('#combat-context').hidden=true;renderGraph(previousTab!==tab);renderInspector();}}catch(e){error(e.message);}finally{requestBusy=false;renderStatus();}}
$('#uniform-step').onclick=()=>act({mode:'uniform'});$('#restart').onclick=()=>act({mode:'restart'});
function renderCurve(){if(!job?.document)return;const root=$('#curve');root.replaceChildren();const data=job.document.duration,N=job.document.horizon,x=t=>30+t/N*445,y=v=>99-v*81;
  for(const v of [0,.5,1]){root.append(svg('line',{x1:30,x2:475,y1:y(v),y2:y(v),stroke:'#e5e9ef','stroke-width':.7}));root.append(svg('text',{x:22,y:y(v)+3,'font-size':8,'text-anchor':'end',fill:'#9ca6b4'},v*100+'%'));}
  const step=(values)=>values.map((p,i)=>`${i?'H'+x(p.t)+' V':'M'+x(p.t)+','}${y(p.v)}`).join(' ');
  const upper=data.map(d=>({t:d.t,v:Math.min(1,d.reference+.05)})),lower=data.map(d=>({t:d.t,v:Math.max(0,d.reference-.05)}));
  let band=step(upper)+` L${x(N)},${y(lower.at(-1).v)}`;for(let i=lower.length-2;i>=0;i--)band+=` H${x(lower[i].t)} V${y(lower[i].v)}`;band+=' Z';root.append(svg('path',{d:band,fill:'#5185d7','fill-opacity':.12}));
  root.append(svg('path',{d:step(data.map(d=>({t:d.t,v:d.reference}))),fill:'none',stroke:'#aeb9c9','stroke-width':2,'stroke-dasharray':'4 4'}));root.append(svg('path',{d:step(data.map(d=>({t:d.t,v:d.actual}))),fill:'none',stroke:'#4274ce','stroke-width':1.7}));
  for(const t of [...new Set([0,1,2,3,4].map(i=>Math.round(i*N/4)))])root.append(svg('text',{x:x(t),y:114,'text-anchor':'middle','font-size':8,fill:'#9ba6b4'},String(t)));}
function renderProofs(){const panel=$('#proof-panel');panel.replaceChildren();if(!job?.document){panel.append(el('p',{class:'proof-intro'},'Generate a candidate to inspect its certificates.'));return;}
  panel.append(el('h3',{},job.status==='verified'?'Accepted by the Lean kernel':'Certificate verification'));
  panel.append(el('p',{class:'proof-intro'},'The external solver proposes rational answers. Lean checks the combat equations, termination paths and links to the game graph. Duration is checked at every event time, using a finite table and a proof for all later times.'));
  for(const title of ['Graph node limit and complete character coverage','3d6 combat mechanics and rendered rows','Almost-sure combat termination','Exact Win / Lose and remaining-HP probabilities','Combat outputs connected to game edges','Eventual defeat within the ±5-point band','Full remaining phase-type duration at the preserved timestamp','No undirected cycle shorter than four','Bound on deterministic actions before strategy mixing']){const row=el('div',{class:'proof-item'});row.append(el('strong',{},title),el('span',{},job.status==='verified'?'PROVED':job.status==='rejected'?'NOT ACCEPTED':'PENDING'));panel.append(row);}
  if(job.document.scene_model_version){for(const title of ['Exactly one active scene per playable state','Scene connections equal projected game transitions','Scene content references exist; no extra actions']){const row=el('div',{class:'proof-item'});row.append(el('strong',{},title),el('span',{},job.status==='verified'?'PROVED':'PENDING'));panel.append(row);}}
  if(job.document.change){for(const title of ['Typed character patch applied exactly','Current node, HP and timestamp preserved','Requested rule transformation checked']){const row=el('div',{class:'proof-item'});row.append(el('strong',{},title),el('span',{},job.status==='verified'?'PROVED':'PENDING'));panel.append(row);}}
  const links=el('div',{class:'downloads'});for(const [ext,label] of [['lean','Lean certificate ↗'],['json','Graph data ↗'],['log','Verifier output ↗']])links.append(el('a',{href:`/download/${job.certificate_id||job.id}.${ext}`,target:'_blank',rel:'noopener'},label));panel.append(links);
  panel.append(el('p',{class:'proof-intro'},'Scope: two fighters; uniform Attack / Defend; ST10 and HT10; HPmax6, current HP 0–3; static fists, knife or broadsword. Timed effects and consumables are not exposed by this prototype. These are exact probabilities with fixed tolerance bands.'));
  panel.append(el('p',{class:'hash'},'MODEL SHA256 '+job.document.model_hash));panel.append(el('p',{class:'hash'},'CERTIFICATE SHA256 '+(job.source_hash||'pending')));
  const details=el('details');details.append(el('summary',{},'Lean output'),el('pre',{},job.log||job.stage));panel.append(details);}
function renderCharacters(){
  const d=job.document;$('#character-panel').hidden=false;
  $('#character-summary').textContent=`${d.characters.length} characters · including the player`;
  const list=$('#character-list');list.replaceChildren();
  for(const c of d.characters){
    const scenes=new Set(d.nodes.filter(n=>n.characters.includes(c.id)).map(n=>n.scene));
    list.append(el('p',{},`${c.name} · ${c.role} · ${scenes.size} events`));
  }
}
function renderCombatPicker(){
  const nodes=job.document.nodes.filter(n=>n.combat), picker=$('#combat-choice');
  picker.replaceChildren();
  for(const node of nodes){
    picker.append(el('option',{value:node.id},`${node.title} · HP ${node.hp} vs ${node.combat.enemy_hp} · node ${node.id}`));
  }
  $('#combat-browser').hidden=!nodes.length;
  if(nodes.some(n=>n.id===job.current))picker.value=job.current;
}
function openSelectedCombat(){
  if(!job?.document)return;
  const id=Number($('#combat-choice').value);
  const node=job.document.nodes.find(n=>n.id===id&&n.combat);
  if(node)return viewCombat(node.combat.entry,node.id);
}
$('#open-combat').onclick=openSelectedCombat;
$('#combat-choice').onchange=()=>{
  if(tab==='combat')openSelectedCombat();
  else if(tab==='adventure'){selected=Number($('#combat-choice').value);renderGraph(false);renderInspector();}
};
$('#locate-combat').onclick=()=>{
  const target=Number($('#combat-choice').value);setTab('adventure');selected=target;renderGraph(false);renderInspector();
  const position=nodePositions.get(selected), rect=$('#graph').getBoundingClientRect();
  if(position){camera={k:1,x:rect.width/2-position.x-76.5,y:rect.height/2-position.y-30};applyCamera();}
};
function rememberJob(){
  try{sessionStorage.setItem('graph-workshop-job',job.id);}catch{}
  const url=new URL(location.href);url.searchParams.set('job',job.id);history.replaceState(null,'',url);
}
function restoreSettings(){
  const d=job.document;difficulty=d.difficulty;
  $$('#difficulty button').forEach(b=>b.classList.toggle('active',b.dataset.value===difficulty));
  $('#target').textContent={easy:'50%',medium:'70%',hard:'90%'}[difficulty];
  $('#branches').value=d.branches;$('#branches').oninput();
  $('#max-nodes').value=d.max_nodes;$('#character-count').value=d.character_count;
}

let ruleProfileKey='', ruleEdgeKey='';
function rulePending(){return ['searching','verifying'].includes(job?.change?.status);}
function renderRules(){
  const panel=$('#rule-panel');panel.hidden=!job?.document;
  if(!job?.document)return;
  const d=job.document, p=d.profile||{dx:12,iq:10,weapon:'punch'};
  const pk=job.id+JSON.stringify(p);
  if(ruleProfileKey!==pk){$('#hero-dx').value=p.dx;$('#hero-iq').value=p.iq;$('#hero-weapon').value=p.weapon;ruleProfileKey=pk;}
  const current=d.nodes[job.current], terminal=['win','lose'].includes(current?.kind);
  const enabled=job.status==='verified'&&!rulePending()&&job.fight==null&&!terminal;
  $('#combat-rule-fields').disabled=!enabled;$('#adventure-rule-fields').disabled=!enabled;
  const edgeKey=job.id+':'+job.current+':'+d.model_hash;
  if(ruleEdgeKey!==edgeKey){
    ruleEdgeKey=edgeKey;const locationPicker=$('#insert-scene');locationPicker.replaceChildren(el('option',{value:''},'Destination’s scene (default)'));for(const s of d.scenes||[])locationPicker.append(el('option',{value:s.id},s.title));locationPicker.append(el('option',{value:'new'},'+ Create a new scene'));const picker=$('#insert-edge');picker.replaceChildren();
    if(!current?.combat){for(const action of d.choices.find(c=>c.state===job.current)?.actions||[]){
      for(const outcome of action.outcomes){const target=d.nodes[outcome.target];if(['win','lose'].includes(target.kind))continue;
        picker.append(el('option',{value:JSON.stringify({action:action.label,destination:outcome.target})},`${action.label} → ${target.title} (${target.id})`));
      }
    }}
    if(!picker.options.length)picker.append(el('option',{value:''},'No eligible ordinary route here'));
  }
  $('#insert-rule-fields').disabled=!enabled||!$('#insert-edge').value;
  $('#rule-clock').textContent=`Event t=${job.timestamp||0} · Node ${job.current} · HP ${current?.hp??'—'}`;
  $('#rules-availability').textContent=job.fight!=null?'Rule changes are locked during combat.':terminal?'This path has ended. Restart the checkpoint or generate a new graph.':`Fixed bands: ±5 points. No undirected triangles. Deterministic actions: ${d.additional?.deterministic??'—'} / ${d.additional?.decisions??'—'} (maximum 90%).`;
  const c=job.change, feedback=$('#rule-feedback');feedback.hidden=!c;
  if(c){feedback.className='rule-feedback '+c.status;feedback.replaceChildren(el('strong',{},c.message));
    if(c.compensation)feedback.append(el('p',{},c.compensation));
    if(c.seconds!=null)feedback.append(el('small',{},`Total: ${c.seconds.toFixed(1)}s`));
  }
  $('#generate').disabled=!serverReady||requestBusy||rulePending();
}
async function changeRule(body){
  if(requestBusy||rulePending())return;
  requestBusy=true;error('');clearTimeout(pollTimer);
  try{job=await api('/api/rules',{id:job.id,revision:job.revision,...body});renderInspector();poll();}
  catch(e){error(e.message);requestBusy=false;renderStatus();}
}
$('#combat-rule-form').onsubmit=e=>{e.preventDefault();changeRule({kind:'combat',dx:Number($('#hero-dx').value),weapon:$('#hero-weapon').value});};
$('#adventure-rule-form').onsubmit=e=>{e.preventDefault();changeRule({kind:'adventure',iq:Number($('#hero-iq').value)});};
$('#insert-rule-form').onsubmit=e=>{e.preventDefault();if($('#insert-edge').value)changeRule({kind:'insert',...JSON.parse($('#insert-edge').value),scene:$('#insert-scene').value||null});};
setTab('scenes');
async function checkServer(){
  try{
    const health=await api('/api/health');
    if(health.version!==4)throw Error('Restart the local server to load the graph generator settings.');
    serverReady=true;$('#generate').disabled=false;error('');
    let saved=new URLSearchParams(location.search).get('job');
    try{saved=saved||sessionStorage.getItem('graph-workshop-job');}catch{}
    if(saved&&/^[a-f0-9]{32}$/.test(saved)){
      job={id:saved};restoringJob=true;requestBusy=true;$('#generate').disabled=true;rememberJob();await poll();
    }
  }catch(e){serverReady=false;$('#generate').disabled=true;error(e.message);setTimeout(checkServer,2000);}
}
checkServer();
