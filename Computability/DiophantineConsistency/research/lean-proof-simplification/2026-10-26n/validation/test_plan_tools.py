#!/usr/bin/env python3
"""Negative tests for replay-plan guards; these do not execute Lean or Lake."""
import copy,json,tempfile,unittest
from pathlib import Path
from plan_tools import inspect_plan,PIN
class PlanTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.b=Path(self.tmp.name)
        (self.b/'a.lean').write_text('namespace DiophantineConsistency.Probe\ntheorem a : True := by trivial\n#print axioms DiophantineConsistency.Probe.a\nend DiophantineConsistency.Probe\n')
        self.plan={'commit':PIN,'probes':[{'source':'a.lean','module':'A','group':'shared','requires_probes':[],'expected':['DiophantineConsistency.Probe.a']}]}
    def tearDown(self):self.tmp.cleanup()
    def check(self):return inspect_plan(self.plan,self.b)['errors']
    def test_valid(self):self.assertFalse(self.check())
    def test_empty(self):self.plan['probes']=[];self.assertTrue(self.check())
    def test_wrong_pin(self):self.plan['commit']='0'*40;self.assertTrue(self.check())
    def test_missing_source(self):self.plan['probes'][0]['source']='absent.lean';self.assertTrue(self.check())
    def test_path_escape(self):self.plan['probes'][0]['source']='../outside.lean';self.assertTrue(self.check())
    def test_missing_expected(self):self.plan['probes'][0]['expected']=[];self.assertTrue(self.check())
    def test_unqualified(self):self.plan['probes'][0]['expected']=['a'];self.assertTrue(self.check())
    def test_missing_print(self):(self.b/'a.lean').write_text('theorem a : True := by trivial\n');self.assertTrue(self.check())
    def test_unaudited_public(self):
        with (self.b/'a.lean').open('a') as f:f.write('theorem b : True := by trivial\n')
        self.assertTrue(self.check())
    def test_sorry(self):
        s=(self.b/'a.lean').read_text().replace('by trivial','by sorry');(self.b/'a.lean').write_text(s);self.assertTrue(self.check())
    def test_comment_sorry_not_code(self):
        with (self.b/'a.lean').open('a') as f:f.write('-- sorry is a forbidden proposal placeholder\n')
        self.assertFalse(self.check())
    def test_duplicate_output(self):self.plan['probes']*=2;self.assertTrue(self.check())
    def test_wrong_dependency_order(self):self.plan['probes'][0]['requires_probes']=['later.lean'];self.assertTrue(self.check())
    def test_cross_world_dependency(self):
        (self.b/'b.lean').write_text('theorem b : True := by trivial\n#print axioms DiophantineConsistency.Probe.b\n')
        self.plan['probes'].append({'source':'b.lean','module':'B','group':'other','requires_probes':['a.lean'],'expected':['DiophantineConsistency.Probe.b']});self.assertTrue(self.check())
    def test_ordered_same_world_dependency(self):
        (self.b/'b.lean').write_text('theorem b : True := by trivial\n#print axioms DiophantineConsistency.Probe.b\n')
        self.plan['probes'].append({'source':'b.lean','module':'B','group':'shared','requires_probes':['a.lean'],'expected':['DiophantineConsistency.Probe.b']});self.assertFalse(self.check())
    def test_bad_module(self):self.plan['probes'][0]['module']='../module';self.assertTrue(self.check())
    def test_duplicate_audit(self):
        with (self.b/'a.lean').open('a') as f:f.write('#print axioms DiophantineConsistency.Probe.a\n')
        self.assertTrue(self.check())
if __name__=='__main__':unittest.main()
