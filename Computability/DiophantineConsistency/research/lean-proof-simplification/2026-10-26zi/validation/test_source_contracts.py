#!/usr/bin/env python3
"""Negative controls for source manifests and declaration-preservation checks."""
import copy,hashlib,json,tempfile,unittest
from pathlib import Path
from source_validate import manifests,blob,declarations,PIN,OLD
from plan_tools import inspect_plan
class SourceContracts(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name);(self.root/'provenance').mkdir()
  for manifest,folder,pin in [('source_manifest.json','sources',PIN),('dependency_manifest.json','dependencies',PIN),('comparison_manifest.json','comparison_sources',OLD)]:
   (self.root/folder).mkdir();(self.root/folder/'a.lean').write_text('theorem a : True := by trivial\n');b=(self.root/folder/'a.lean').read_bytes()
   (self.root/'provenance'/manifest).write_text(json.dumps({'commit':pin,'sources':[{'path':'a.lean','sha':blob(b),'sha256':hashlib.sha256(b).hexdigest()}]}))
 def tearDown(self):self.tmp.cleanup()
 def errors(self):return [e for r in manifests(self.root) for e in r['errors']]
 def edit(self,fn):
  path=self.root/'provenance/source_manifest.json';m=json.loads(path.read_text());fn(m);path.write_text(json.dumps(m))
 def test_valid_manifests(self):self.assertFalse(self.errors())
 def test_changed_bytes(self):(self.root/'sources/a.lean').write_text('theorem a : False := by sorry');self.assertTrue(self.errors())
 def test_missing_bytes(self):(self.root/'dependencies/a.lean').unlink();self.assertTrue(self.errors())
 def test_wrong_pin(self):self.edit(lambda m:m.update(commit=OLD));self.assertTrue(self.errors())
 def test_duplicate(self):self.edit(lambda m:m['sources'].extend(copy.deepcopy(m['sources'])));self.assertTrue(self.errors())
 def test_empty(self):self.edit(lambda m:m.update(sources=[]));self.assertTrue(self.errors())
 def test_escape(self):self.edit(lambda m:m['sources'][0].update(path='../outside.lean'));self.assertTrue(self.errors())
 def test_signature_negative_control(self):self.assertNotEqual(declarations('theorem a (n : Nat) : n = n := by rfl'),declarations('theorem a (n : Nat) (h : n > 0) : n = n := by rfl'))
 def test_definition_negative_control(self):self.assertNotEqual(declarations('def word := actualWord\nend X'),declarations('def word := otherWord\nend X'))
 def test_proof_rewrite_preserves_statement(self):self.assertEqual(declarations('theorem a : True := by trivial\nend X'),declarations('theorem a : True := True.intro\nend X'))
 def test_overlay_order_detected_without_declared_dependency(self):
  (self.root/'a.lean').write_text('import DiophantineConsistency.B\ntheorem a : True := by trivial\n#print axioms DiophantineConsistency.A.a\n')
  (self.root/'b.lean').write_text('theorem b : True := by trivial\n#print axioms DiophantineConsistency.B.b\n')
  a={'source':'a.lean','module':'DiophantineConsistency.A','group':'composed','expected':['DiophantineConsistency.A.a']}
  b={'source':'b.lean','module':'DiophantineConsistency.B','group':'composed','expected':['DiophantineConsistency.B.b']}
  errors=inspect_plan({'commit':PIN,'probes':[a,b]},self.root)['errors']
  self.assertTrue(any('overlay import not earlier' in e for e in errors));self.assertTrue(any('undeclared overlay' in e for e in errors))
 def test_missing_declaration_of_prior_overlay_dependency(self):
  (self.root/'a.lean').write_text('theorem a : True := by trivial\n#print axioms DiophantineConsistency.A.a\n')
  (self.root/'b.lean').write_text('import DiophantineConsistency.A\ntheorem b : True := by trivial\n#print axioms DiophantineConsistency.B.b\n')
  plan={'commit':PIN,'probes':[{'source':'a.lean','module':'DiophantineConsistency.A','group':'composed','expected':['DiophantineConsistency.A.a']},{'source':'b.lean','module':'DiophantineConsistency.B','group':'composed','expected':['DiophantineConsistency.B.b']}]}
  self.assertTrue(any('undeclared overlay' in e for e in inspect_plan(plan,self.root)['errors']))
if __name__=='__main__':unittest.main()
