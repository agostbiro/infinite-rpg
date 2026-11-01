import {test} from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {environmentFor,placeForScene,eventAnchorForScene,worldLayout,sceneryFor,propRadius,moveInWorld} from '../web/environment.js';
import {portalsForView, crossedPortal, themeFor} from '../web/spatial.js';
const campaign=JSON.parse(fs.readFileSync(new URL('../campaigns/napoleon.json',import.meta.url)));
const forest={theme:'forest',places:[{id:9,name:'Pine Camp',kind:'camp',x:-40,z:30},{id:3,name:'Hidden Ruins',kind:'ruins',x:40,z:-30}],paths:[{fromPlace:9,toPlace:3}],props:[{kind:'tree',x:-50,z:-40,scale:200,heading:0}],scenes:[{scene:42,place:3}]};
const sampleView={phase:'scene',inputs:[{choose:{choice:0}},{choose:{choice:1}}],scene:{id:42,choices:[{text:'Read the map',input:{choose:{choice:0}}},{text:'Talk to the guide',input:{choose:{choice:1}}}]}};

test('different Wish worlds use their own coordinates, scene mappings and themes',()=>{
  assert.equal(placeForScene(forest,42).name,'Hidden Ruins');
  assert.equal(themeFor({environment:forest,adventure:'Desert story'}).name,'Woodland');
  assert.equal(environmentFor({environment:forest}),forest);
  assert.notDeepEqual(forest.places,campaign.environment.places);
  assert.equal(campaign.environment.scenes.length,campaign.scenes.length);
  for(const scene of campaign.scenes) assert.ok(campaign.environment.scenes.find(s=>s.scene===scene.id));
});

test('every declared world trail and every current option is physically reachable',()=>{
  for(const environment of [campaign.environment,forest]) {
    const obstacles=sceneryFor(environment).filter(p=>p.kind!=='river').map(p=>({...p,radius:propRadius(p)}));
    for(const path of environment.paths) {
      const a=environment.places.find(p=>p.id===path.fromPlace),b=environment.places.find(p=>p.id===path.toPlace);
      let position={x:a.x,z:a.z};
      const steps=Math.ceil(Math.hypot(b.x-a.x,b.z-a.z)*4);
      for(let i=0;i<steps;i++) position=moveInWorld(position,(b.x-a.x)/steps,(b.z-a.z)/steps,obstacles);
      assert.ok(Math.hypot(position.x-b.x,position.z-b.z)<0.01, `${a.name} → ${b.name}`);
    }
    for(const place of environment.places) {
      const layout=worldLayout(portalsForView(sampleView),place);
      assert.deepEqual(layout.portals.map(p=>p.input),sampleView.inputs);
      for(const target of layout.portals) {
        let position={x:target.x,z:place.z+5};
        let selected=null;
        for(let i=0;i<40&&!selected;i++) {
          const next=moveInWorld(position,0,-0.25,obstacles);
          selected=crossedPortal(position,next,layout.portals);position=next;
        }
        assert.equal(selected?.key,target.key);
      }
    }
  }
});

test('continuous movement leaves graph inputs untouched and cannot cross solid scenery',()=>{
  const before=JSON.stringify(sampleView);
  const wall=[{x:0,z:0,radius:3}];
  const p=moveInWorld({x:0,z:10},0,-20,wall);
  assert.ok(p.z>=3.4);
  const edge=moveInWorld({x:100,z:100},100,100,[]);
  assert.deepEqual(edge,{x:115,z:115});
  assert.equal(JSON.stringify(sampleView),before);
});

test('English campaign content and exact scene coverage are supplied as data',()=>{
  assert.equal(campaign.title,'Bonaparte · Maps of the Nile');
  assert.ok(campaign.scenes.every(s=>!/[éèàùœ]|\b(?:vous|votre|Parler|Retourner)\b/.test(s.text+' '+s.title)));
  const ids=campaign.environment.scenes.map(s=>s.scene);
  assert.equal(new Set(ids).size,campaign.scenes.length);
  assert.deepEqual([...ids].sort((a,b)=>a-b),campaign.scenes.map(s=>s.id).sort((a,b)=>a-b));
});


test('story events visit every place and do not cluster the campaign at one objective',()=>{
  const e=campaign.environment;
  const location=new Map(e.scenes.map(s=>[s.scene,s.place]));
  assert.equal(new Set(location.values()).size,e.places.length);
  const edges=campaign.scenes.flatMap(s=>s.choices.flatMap(c=>{
    const o=c.outcome;
    const targets=o.type==='goto'?[o.next]:o.type==='fight'?[o.onWin]:[o.onSuccess,o.onFailure];
    return targets.map(t=>[s.id,t]);
  }));
  assert.ok(edges.filter(([u,v])=>location.get(u)!==location.get(v)).length*3>=edges.length);
  const has=(u,v)=>edges.some(([a,b])=>a===u&&b===v);
  for(const [u,v] of edges) {
    assert.notEqual(u,v);
    assert.ok(!has(v,u));
    for(const [a,w] of edges) if(a===v) assert.ok(!has(w,u), `${u} → ${v} → ${w} → ${u}`);
  }
});

test('event offsets vary within a place and every shifted interaction stays accessible',()=>{
  const e=campaign.environment;
  assert.notDeepEqual(eventAnchorForScene(e,0),eventAnchorForScene(e,1));
  const obstacles=sceneryFor(e).filter(p=>p.kind!=='river').map(p=>({...p,radius:propRadius(p)}));
  for(const scene of campaign.scenes) {
    const inputs=scene.choices.map((_,choice)=>({choose:{choice}}));
    const view={phase:'scene',inputs,scene:{...scene,choices:scene.choices.map((c,i)=>({...c,input:inputs[i]}))}};
    const place=placeForScene(e,scene.id), anchor=eventAnchorForScene(e,scene.id);
    const layout=worldLayout(portalsForView(view),place,null,anchor);
    assert.deepEqual(layout.portals.map(p=>p.input),inputs);
    for(const target of layout.portals) {
      assert.ok(Math.hypot(target.x-place.x,target.z-place.z)<9.3);
      let p={x:target.x,z:target.z+2.2},selected=null;
      for(let i=0;i<12&&!selected;i++) {
        const next=moveInWorld(p,0,-0.2,obstacles);
        selected=crossedPortal(p,next,layout.portals); p=next;
      }
      assert.equal(selected?.key,target.key);
    }
  }
});
