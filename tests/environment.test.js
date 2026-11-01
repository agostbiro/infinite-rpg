import {test} from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {environmentFor,placeForScene,worldLayout,sceneryFor,propRadius,moveInWorld} from '../web/environment.js';
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
