import copy
import tempfile
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
import unittest
from fractions import Fraction as Q
import engine, rules, server, certificate, scenes

class LiveRulesTests(unittest.TestCase):
    def snapshot(self,difficulty='easy'):
        d,w,r,c=engine.generate(difficulty,2,30,4)
        return dict(document=d,world=w,ref=r,duel=c,current=0,timestamp=0,fight=None,revision=0,status='verified',history=[])

    def test_three_changes_and_frozen_contract(self):
        for difficulty in ('easy','medium','hard'):
            s=self.snapshot(difficulty);before=copy.deepcopy(s)
            for req in [dict(kind='combat',dx=13,weapon='largeKnife'),dict(kind='adventure',iq=14),
                        dict(kind='insert',action=next(iter(s['world']['choices'][0])),destination=1)]:
                d,w,r,c=rules.propose(s,req)
                self.assertEqual(s,before)
                self.assertEqual(r['rows'],s['ref']['rows'])
                self.assertEqual(d['target'],s['document']['target']);self.assertEqual(d['epsilon'],s['document']['epsilon'])
                self.assertEqual(d['profile']['iq'],req.get('iq',10));self.assertEqual(d['profile']['dx'],req.get('dx',12))
                self.assertTrue(d['additional']['no_small_cycles'])
                self.assertLessEqual(abs(Q(d['exact_loss'])-Q(d['target'])),Q(1,20))
                code=certificate.export(d,w,r,c,previous=s)
                self.assertIn('theorem rule_admitted',code);self.assertIn('theorem session_preserved',code)
                self.assertNotIn('sorry',code)

    def test_adventure_changes_actions_not_combat(self):
        s=self.snapshot();d,w,r,c=rules.propose(s,dict(kind='adventure',iq=14))
        self.assertEqual(c,s['duel']);self.assertEqual(w['rows'],s['world']['rows'])
        self.assertNotEqual(w['choices'],s['world']['choices'])
        for i,n in enumerate(w['nodes']):
            if n['scene']=='shrine':
                heal=next(v for v in w['rows'][i] if w['nodes'][v]['scene']=='rest')
                self.assertEqual(w['choices'][i]['Careful recovery'][heal],Q(7,10))
                self.assertEqual(w['choices'][i]['Bold recovery'][heal],Q(3,10))

    def test_weapon_rebuilds_complete_exit_law(self):
        s=self.snapshot();d,w,r,c=rules.propose(s,dict(kind='combat',dx=13,weapon='largeKnife'))
        self.assertNotEqual(c['rows'],s['duel']['rows'])
        for n in w['nodes']:
            if 'combat' in n:
                for v,p in w['rows'][n['id']].items():
                    self.assertEqual(p,c['exits'][n['combat']['entry']][w['nodes'][v]['hp']])
            else:self.assertEqual(w['choices'][n['id']],s['world']['choices'][n['id']])

    def test_insertion_is_real_and_no_shortcut(self):
        s=self.snapshot();a=next(iter(s['world']['choices'][0]));d,w,r,c=rules.propose(s,dict(kind='insert',action=a,destination=1))
        fresh=len(s['world']['nodes']);self.assertEqual(len(w['nodes']),fresh+1)
        self.assertEqual(w['choices'][0][a],{fresh:Q(1)});self.assertEqual(w['rows'][fresh],{1:Q(1)})
        self.assertEqual([x[0] for x in w['table'][:len(s['world']['table'])]],[x[0] for x in s['world']['table']])

    def test_nonzero_timestamp(self):
        s=self.snapshot();server.do_action(s,dict(revision=0,mode='choice',action=next(iter(s['world']['choices'][0]))))
        self.assertEqual(s['timestamp'],1)
        d,w,r,c=rules.propose(s,dict(kind='adventure',iq=12))
        self.assertEqual(d['timestamp'],1);self.assertEqual(d['first_state'],s['current'])
        self.assertIn('(t := 1)',certificate.export(d,w,r,c,previous=s))
        with self.assertRaises(ValueError):rules.remaining_curve(w,r,s['current'],0,Q(1,20))

    def test_combat_and_stale_commands_rejected(self):
        s=self.snapshot();s['fight']=engine.encode((3,2,0,0));before=copy.deepcopy(s)
        with self.assertRaisesRegex(ValueError,'combat'):rules.propose(s,dict(kind='adventure',iq=12))
        with self.assertRaisesRegex(ValueError,'combat'):server.start_change(s,dict(revision=0,kind='adventure',iq=12))
        self.assertEqual(s,before);s['fight']=None
        with self.assertRaisesRegex(ValueError,'advanced'):server.start_change(s,dict(revision=-1,kind='adventure',iq=12))
        s['change']={'status':'verifying'}
        with self.assertRaisesRegex(ValueError,'Wait'):server.do_action(s,dict(revision=0,mode='uniform'))

    def test_exact_persistence(self):
        s=self.snapshot();r=server.decode_saved(server.encode_saved(s))
        self.assertEqual(r['world']['choices'],s['world']['choices']);self.assertEqual(r['duel']['exits'],s['duel']['exits'])

    def test_invalid_requests_and_triangles(self):
        s=self.snapshot()
        for req in [dict(kind='combat',dx=True,weapon='punch'),dict(kind='combat',dx=13,weapon='unknown'),
                    dict(kind='adventure',iq=20),dict(kind='insert',action='missing',destination=1)]:
            with self.assertRaises(ValueError):rules.propose(s,req)
        w=copy.deepcopy(s['world']);w['rows'][0][4]=Q(1,10)
        with self.assertRaisesRegex(ValueError,'triangle'):engine.additional_checks(w,Q(9,10))

    def test_lean_failure_never_installs_candidate(self):
        s=self.snapshot();s['id']='test';s['change']={'id':'candidate','status':'searching'}
        before=copy.deepcopy(s)
        with tempfile.TemporaryDirectory() as tmp, patch.object(server,'GENERATED',Path(tmp)), patch.object(server.subprocess,'run',return_value=SimpleNamespace(returncode=1,stdout='rejected',stderr='')):
            server.run_change(s,copy.deepcopy(s),dict(kind='adventure',iq=12),'candidate')
        for field in ('world','document','duel','ref','current','timestamp','revision'):
            self.assertEqual(s[field],before[field])
        self.assertEqual(s['change']['status'],'rejected')

    def test_failure_to_save_never_installs_candidate(self):
        s=self.snapshot();s['id']='test';s['change']={'id':'candidate','status':'searching'}
        before=copy.deepcopy(s)
        # Unit-test atomic commit, independently of the real Lean integration tests.
        proofnames=['combat_mechanics','combat_outputs','exit_exact','world_terminates','loss_exact',
                    'bernoulli_fair','timestamp_fair','additional_properties','actions_match_graph','rule_admitted',
                    'player_patch_exact','session_preserved','node_states_preserved','actual_player_input',
                    'combat_uses_actual_player','characters_well_formed','rule_scope']
        proofnames += list(scenes.PROOF_NAMES)
        proofnames += [f'{prefix}_{n["id"]}' for n in s['world']['nodes'] if 'combat' in n
                       for prefix in ('collapsed_combat','combat_balanced')]
        fake=SimpleNamespace(returncode=0,stdout='\n'.join('WorkshopCertificate.'+n for n in proofnames),stderr='')
        with tempfile.TemporaryDirectory() as tmp, patch.object(server,'GENERATED',Path(tmp)), patch.object(server.subprocess,'run',return_value=fake), patch.object(server,'persist',side_effect=[OSError('disk full'),None]):
            server.run_change(s,copy.deepcopy(s),dict(kind='adventure',iq=12),'candidate')
        for field in ('world','document','duel','ref','current','timestamp','revision'):
            self.assertEqual(s[field],before[field])
        self.assertEqual(s['change']['status'],'rejected')

if __name__=='__main__':unittest.main()
