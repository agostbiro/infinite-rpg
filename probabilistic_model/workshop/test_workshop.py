import copy
import unittest
from fractions import Fraction as Q
import engine
import certificate
import server


class ExactWorkshopTests(unittest.TestCase):
    def test_difficulties_and_complete_duration(self):
        for difficulty in ("easy", "medium", "hard"):
            for branches in (2, 3, 4):
                d, w, r, c = engine.generate(difficulty, branches, max_nodes=19+branches)
                self.assertLessEqual(abs(w["losses"][0] - Q(d["target"])), Q(1,20))
                self.assertTrue(all(x == 1 for x in w["table"][-1]))
                self.assertEqual([row[0] for row in w["table"]], [row[0] for row in r["table"]])
                for s, row in enumerate(w["rows"]):
                    self.assertEqual(sum(row.values(),Q(0)),1)
                    self.assertEqual(row,engine.uniform_row(w["choices"][s]))
                    self.assertTrue(all(p > 0 for p in row.values()))

    def test_combat_outputs_depend_on_actual_entry_hp(self):
        c=engine.combat(12)
        wounded=c["exits"][engine.encode((1,2,0,0))][0]
        healthy=c["exits"][engine.encode((3,2,0,0))][0]
        self.assertGreater(wounded,healthy)
        for s, row in enumerate(c["rows"]):
            self.assertEqual(row,engine.combine(c["raw_rows"][s]))
            if not c["terminal"][s]:
                self.assertTrue(all(engine.decode(v)[2] != engine.decode(s)[2] for v in row))

    def test_defense_preserves_hp_and_gives_opponent_turn(self):
        for turn in (0,1):
            s=(2,3,turn,0)
            row=engine.combat_actions(s,12)["Defend"]
            self.assertEqual(row,{engine.encode((2,3,1-turn,1)):Q(1)})

    def test_visual_edges_are_the_verified_rows(self):
        d,w,_,_=engine.generate("medium",3)
        observed={}
        for edge in d["edges"]:
            observed.setdefault(edge["source"],{})[edge["target"]]=Q(edge["probability"])
        self.assertEqual([observed[i] for i in range(len(w["rows"]))],w["rows"])

    def test_play_gate_and_revision(self):
        d,w,r,c=engine.generate()
        job=dict(status="verifying",revision=0,current=0,fight=None,history=[],document=d,world=w,duel=c)
        with self.assertRaisesRegex(ValueError,"Lean"):
            server.do_action(job,dict(revision=0,mode="uniform"))
        job["status"]="verified"  # Unit fixture; end-to-end tests obtain a real certificate.
        server.do_action(job,dict(revision=0,mode="uniform"))
        with self.assertRaisesRegex(ValueError,"advanced"):
            server.do_action(job,dict(revision=0,mode="uniform"))
        server.do_action(job,dict(revision=1,mode="restart"))
        self.assertEqual(job["current"],0)
        self.assertEqual(job["revision"],2)

    def test_combat_exit_carries_hp_into_adventure(self):
        d,w,r,c=engine.generate(max_nodes=21)
        job=dict(status="verified",revision=0,current=1,fight=None,history=[],document=d,world=w,duel=c)
        server.do_action(job,dict(revision=0,mode="startCombat"))
        self.assertEqual(engine.decode(job["fight"])[0],w["nodes"][1]["hp"])
        for _ in range(2000):
            if job["fight"] is None:
                break
            before=job["fight"]
            server.do_action(job,dict(revision=job["revision"],mode="uniform"))
            if job["fight"] is None:
                hp=w["nodes"][job["current"]]["hp"]
                self.assertTrue(any(c["outputs"][v]==hp and c["terminal"][v] for v in c["rows"][before]))
        self.assertIsNone(job["fight"])

    def test_node_budget_characters_and_variable_horizon(self):
        for difficulty, branches, limit, count in (("easy",2,21,2),("medium",3,31,7),("hard",4,60,12)):
            d,w,r,c=engine.generate(difficulty,branches,limit,count)
            self.assertEqual(len(w["nodes"]),limit)
            self.assertEqual(len(d["characters"]),count)
            self.assertEqual({i for n in d["nodes"] for i in n["characters"]},set(range(count)))
            self.assertEqual(d["horizon"],len(w["table"])-1)
            self.assertTrue(all(x==1 for x in w["table"][-1]))
            self.assertEqual([x[0] for x in w["table"]],[x[0] for x in r["table"]])
            self.assertLessEqual(abs(w["losses"][0]-Q(d["target"])),Q(1,20))
            reachable={0}
            todo=[0]
            while todo:
                for v in w["rows"][todo.pop()]:
                    if v not in reachable:
                        reachable.add(v)
                        todo.append(v)
            self.assertEqual(reachable,set(range(limit)))
            for n in w["nodes"]:
                if "combat" in n:
                    self.assertIn(n["combat"]["opponent"],n["characters"])
                    self.assertGreater(n["combat"]["opponent"],0)
            code=certificate.export(d,w,r,c)
            self.assertIn("theorem generation_size",code)
            self.assertIn("theorem character_coverage",code)
            self.assertIn(f"reference {d['horizon']} reference_last",code)
            self.assertNotIn("sorry",code)
            self.assertNotIn("native_decide",code)

    def test_invalid_limits_are_rejected(self):
        for args in (dict(max_nodes=20),dict(branches=4,max_nodes=22),dict(max_nodes=61),
                     dict(max_nodes=24.5),dict(character_count=1),dict(character_count=13),
                     dict(character_count=True),dict(branches=True)):
            with self.subTest(args=args),self.assertRaises(ValueError):
                engine.generate(**args)

    def test_new_settings_change_the_actual_graph(self):
        a,_,_,_=engine.generate(max_nodes=21,character_count=2)
        b,_,_,_=engine.generate(max_nodes=30,character_count=8)
        self.assertGreater(len(b["nodes"]),len(a["nodes"]))
        self.assertGreater(b["horizon"],a["horizon"])
        self.assertNotEqual(a["duration"],b["duration"])
        self.assertNotIn("wish",b)
        self.assertNotIn("theme",b)

if __name__=='__main__':
    unittest.main()
