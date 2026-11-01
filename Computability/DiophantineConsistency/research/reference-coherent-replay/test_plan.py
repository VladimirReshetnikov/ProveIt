#!/usr/bin/env python3
"""Small negative controls for the source-only replay planner."""
from pathlib import Path
import tempfile
import unittest
import plan as p

class PlanTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        self.src=self.root/'src';self.snap=self.root/'snapshot';self.src.mkdir();self.snap.mkdir()
        self.libs={'P':self.src};self.targets=['P.C']
        self.write(self.src/'P/A.lean','prelude\n')
        self.write(self.src/'P/B.lean','import P.A\n')
        self.write(self.src/'P/C.lean','import P.B\n')
        self.write(self.snap/'src/P/A.lean','prelude\n')
        self.write(self.snap/'src/P/B.lean','import P.A\n')
        self.parent={'status':'FROZEN_NOT_COMPILED','project_modules':2,'order':['P.A','P.B'],
            'sources':{name:{'snapshot_path':f'src/P/{name[-1]}.lean',
                'workspace_path':f'src/P/{name[-1]}.lean',
                'sha256':p.sha((self.src/f'P/{name[-1]}.lean').read_bytes()),
                'imports':p.imports((self.src/f'P/{name[-1]}.lean').read_bytes())} for name in ('P.A','P.B')}}
    def tearDown(self):self.tmp.cleanup()
    def write(self,path,text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    def go(self,basis='current',drafts=None):
        return p.plan(self.root,self.snap,self.parent,self.libs,self.targets,drafts or {},basis)
    def test_closure_and_modes(self):
        got=self.go();self.assertEqual(got['order'],['P.A','P.B','P.C'])
        self.assertEqual(got['additional_project_modules'],['P.C'])
        self.assertEqual(got['parent_source_drift'],[])
    def test_current_refuses_ancestor_drift_historical_records_it(self):
        self.write(self.src/'P/A.lean','prelude\n-- changed\n')
        with self.assertRaisesRegex(ValueError,'parent source drift'):self.go()
        got=self.go('historical');self.assertEqual(got['parent_source_drift'],['P.A'])
        self.assertEqual(got['sources']['P.A']['source_sha256'],self.parent['sources']['P.A']['sha256'])
    def test_tampered_parent_snapshot_rejected(self):
        self.write(self.snap/'src/P/A.lean','prelude\n-- bad\n')
        with self.assertRaisesRegex(ValueError,'parent source mismatch'):self.go()
    def test_manifest_only_is_explicitly_unchecked(self):
        self.write(self.snap/'src/P/A.lean','prelude\n-- bad\n')
        got=p.plan(self.root,self.snap,self.parent,self.libs,self.targets,{},'historical',True)
        self.assertEqual(got['status'],'PROVISIONAL_MANIFEST_PLAN')
        self.assertIsNone(got['parent_source_drift'])
        self.assertIsNone(got['sources']['P.A']['current_workspace_sha256'])
        with self.assertRaisesRegex(ValueError,'requires historical'):
            p.plan(self.root,self.snap,self.parent,self.libs,self.targets,{},'current',True)
    def test_changed_header_and_cycle_rejected(self):
        self.write(self.src/'P/C.lean','import P.C\n')
        with self.assertRaisesRegex(ValueError,'import cycle'):self.go()
    def test_draft_cannot_shadow_live_source(self):
        draft=self.root/'draft/C.lean';self.write(draft,'import P.B\n')
        with self.assertRaisesRegex(ValueError,'draft shadows live source'):self.go(drafts={'P.C':draft})
    def test_comments_and_unsupported_import(self):
        self.assertEqual(p.imports(b'/- import P.Fake -/\nimport P.A -- comment\n'),['P.A'])
        with self.assertRaisesRegex(ValueError,'unsupported import'):p.imports(b'import P.A; evil\n')

if __name__=='__main__':unittest.main()
