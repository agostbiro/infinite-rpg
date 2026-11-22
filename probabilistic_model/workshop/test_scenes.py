import copy
import unittest
from unittest.mock import patch
import engine
import scenes
import rules
import server
from fractions import Fraction as Q


class SceneTests(unittest.TestCase):
    def snapshot(self):
        d,w,r,c = engine.generate(max_nodes=30, character_count=6)
        return dict(document=d,world=w,ref=r,duel=c,current=0,timestamp=0,
                    fight=None,revision=0,status='verified',history=[])

    def test_membership_contents_and_no_gameplay_change(self):
        s = self.snapshot(); w = s['world']; before = copy.deepcopy(w)
        scenes.attach(w, s['document'])
        self.assertEqual(w, before)
        for n in w['nodes']:
            locations = [x for x in w['scenes'] if n['id'] in x['states']]
            self.assertEqual(len(locations), 0 if w['terminal'][n['id']] else 1)
            variants = [v for v in w['nodes'] if v['scene'] == n['scene']]
            self.assertEqual({v['scene_id'] for v in variants}, {n['scene_id']})
        self.assertTrue(any(len(x['events']) > 1 for x in w['scenes']))
        self.assertTrue(all(i['kind'] == 'reusable' for i in w['scene_items']))

    def test_projection_exact_and_internal_transition_retained(self):
        s = self.snapshot(); w = s['world']; d = s['document']
        projected = {(e['source'], e['target']) for e in d['scene_edges']}
        expected = set(); internal = False
        for u,row in enumerate(w['rows']):
            for v,p in row.items():
                a,b = w['nodes'][u]['scene_id'], w['nodes'][v]['scene_id']
                if p > 0 and a is not None and b is not None:
                    if a != b: expected.add((a,b))
                    elif u != v: internal = True
        self.assertEqual(projected, expected)
        self.assertTrue(internal)
        for e in d['scene_edges']:
            self.assertTrue(e['witnesses'])
            for witness in e['witnesses']:
                self.assertGreater(w['rows'][witness['source']][witness['target']],0)

    def test_same_scene_does_not_enable_other_events(self):
        s=self.snapshot(); w=s['world']
        # Two successive exploration layers share a scene but have different choices.
        v=next(n['id'] for n in w['nodes'] if n['scene']=='event:0:0')
        other=next(n['id'] for n in w['nodes'] if n['scene']=='event:1:0')
        self.assertEqual(w['nodes'][v]['scene_id'],w['nodes'][other]['scene_id'])
        action=next(iter(w['choices'][other]));self.assertNotIn(action,w['choices'][v])
        s['current']=v
        with self.assertRaisesRegex(ValueError,'not available'):
            server.do_action(s,dict(revision=0,mode='choice',action=action))

    def test_insert_existing_or_new_scene_and_update_edges(self):
        for location in ('camp','new',None):
            s=self.snapshot();before=copy.deepcopy(s)
            action=next(iter(s['world']['choices'][0]))
            d,w,_,_=rules.propose(s,dict(kind='insert',action=action,destination=1,scene=location))
            self.assertEqual(s,before)
            fresh=len(before['world']['nodes']);new=w['nodes'][fresh]['scene_id']
            self.assertEqual([n['scene_id'] for n in w['nodes'][:fresh]],
                             [n['scene_id'] for n in before['world']['nodes']])
            self.assertEqual(len(d['scenes']),len(before['document']['scenes'])+(location=='new'))
            if location=='new':
                self.assertIn(('camp',new),{(e['source'],e['target']) for e in d['scene_edges']})
                self.assertIn((new,w['nodes'][1]['scene_id']),{(e['source'],e['target']) for e in d['scene_edges']})
            elif location=='camp': self.assertEqual(new,'camp')
            else: self.assertEqual(new,w['nodes'][1]['scene_id'])
        s=self.snapshot()
        with self.assertRaisesRegex(ValueError,'existing scene'):
            rules.propose(s,dict(kind='insert',action=next(iter(s['world']['choices'][0])),destination=1,scene='missing'))

    def test_removed_last_connection_is_not_retained(self):
        s=self.snapshot();w=s['world'];d=s['document']
        edge=d['scene_edges'][0]
        for witness in edge['witnesses']:
            del w['rows'][witness['source']][witness['target']]
        scenes.attach(w,d)
        self.assertNotIn((edge['source'],edge['target']),{(e['source'],e['target']) for e in d['scene_edges']})

    def test_conflicting_variant_and_missing_content_rejected(self):
        s=self.snapshot();w=s['world']
        n=next(n for n in w['nodes'] if n['scene']=='shrine');n['scene_id']='camp'
        with self.assertRaisesRegex(ValueError,'variants'):scenes.attach(w,s['document'])
        s=self.snapshot();s['world']['scenes'][0]['objects']=[999999]
        with self.assertRaisesRegex(ValueError,'unknown'):scenes.attach(s['world'],s['document'])

    def test_scene_triangle_allowed_when_event_graph_has_no_small_cycles(self):
        # Four distinct events along a path visit A -> B -> C -> A.
        # The event graph is acyclic; its scene projection has a triangle.
        w=dict(nodes=[dict(id=i, scene=f'e{i}', scene_id=s, column=i, characters=[0])
                      for i,s in enumerate(['A','B','C','A',None])],
               rows=[{1:Q(1)},{2:Q(1)},{3:Q(1)},{4:Q(1)},{4:Q(1)}],
               terminal=[False,False,False,False,True])
        w['choices']=[{'Continue':row} for row in w['rows']]
        d=dict(characters=[dict(id=0,name='Player')])
        self.assertTrue(engine.additional_checks(w,Q(1))['no_small_cycles'])
        scenes.attach(w,d)
        self.assertEqual({(e['source'],e['target']) for e in d['scene_edges']},
                         {('A','B'),('B','C'),('C','A')})


if __name__=='__main__':unittest.main()
