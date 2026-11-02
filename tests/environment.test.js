import {test} from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {environmentFor,placeForScene,eventAnchorForScene,worldLayout,sceneryFor,propRadius,moveInWorld} from '../web/environment.js';
import {portalsForView, themeFor, interactionPoints, nearestPoint, pointRadius} from '../web/spatial.js';
import {arrivalForLayout} from '../web/travel.js';
// A small story and its world map, only for these tests.
const campaign=JSON.parse(fs.readFileSync(new URL('./spatial-world.json',import.meta.url)));
const forest={theme:'forest',places:[{id:9,name:'Pine Camp',kind:'camp',x:-40,z:30},{id:3,name:'Hidden Ruins',kind:'ruins',x:40,z:-30}],paths:[{fromPlace:9,toPlace:3}],props:[{kind:'tree',x:-50,z:-40,scale:200,heading:0}],scenes:[{scene:42,place:3}]};
/** Walk straight from the arrival of `layout` toward `target`, around solid scenery, people and
 * objects. Returns `true` when the menu of `target` shows. */
function reachesMenu(layout,target,scenery) {
  const solid=[...scenery,...layout.points.map(p=>({x:p.x,z:p.z,radius:pointRadius(p)}))];
  let position=arrivalForLayout(layout);
  for(let i=0;i<400;i++) {
    if(nearestPoint(position,layout.points)?.id===target.id) return true;
    const dx=target.x-position.x,dz=target.z-position.z,d=Math.hypot(dx,dz);
    position=moveInWorld(position,dx/d*0.05,dz/d*0.05,solid,layout.bound);
  }
  return false;
}
/** The inputs held by the points of a layout, in order. */
const inputsOf=layout=>layout.points.flatMap(p=>p.actions.map(a=>a.input));
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
      const layout=worldLayout(interactionPoints(sampleView,portalsForView(sampleView)),place);
      assert.deepEqual(inputsOf(layout),sampleView.inputs);
      for(const target of layout.points) assert.ok(reachesMenu(layout,target,obstacles),`${place.name}: ${target.id}`);
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

test('the map gives each Scene exactly one place, and every place hosts a Scene',()=>{
  const e=campaign.environment;
  const ids=e.scenes.map(s=>s.scene);
  assert.equal(new Set(ids).size,campaign.scenes.length);
  assert.deepEqual([...ids].sort((a,b)=>a-b),campaign.scenes.map(s=>s.id).sort((a,b)=>a-b));
  assert.equal(new Set(e.scenes.map(s=>s.place)).size,e.places.length);
});

test('event offsets vary within a place and every shifted interaction stays accessible',()=>{
  const e=campaign.environment;
  assert.notDeepEqual(eventAnchorForScene(e,3),eventAnchorForScene(e,4));
  const obstacles=sceneryFor(e).filter(p=>p.kind!=='river').map(p=>({...p,radius:propRadius(p)}));
  for(const scene of campaign.scenes) {
    const inputs=scene.choices.map((_,choice)=>({choose:{choice}}));
    const view={phase:'scene',inputs,scene:{...scene,choices:scene.choices.map((c,i)=>({...c,input:inputs[i]}))}};
    const place=placeForScene(e,scene.id), anchor=eventAnchorForScene(e,scene.id);
    const layout=worldLayout(interactionPoints(view,portalsForView(view)),place,null,anchor);
    assert.deepEqual([...inputsOf(layout)].map(i=>i.choose.choice).sort(),inputs.map(i=>i.choose.choice));
    for(const target of layout.points) {
      assert.ok(Math.hypot(target.x-place.x,target.z-place.z)<9.3);
      if(target.actions.length) assert.ok(reachesMenu(layout,target,obstacles),`scene ${scene.id}: ${target.id}`);
    }
  }
});
