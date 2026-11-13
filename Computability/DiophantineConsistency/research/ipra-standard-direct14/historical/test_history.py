#!/usr/bin/env python3
"""Negative controls for historical parent and added-source Git binding."""
if not __debug__:
    raise RuntimeError('controls require Python assertions enabled')

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import prepare

H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.base=Path(self.tmp.name)
        self.root=self.base/'workspace';self.root.mkdir()
        self.git('init','-q')
        self.write('lakefile.toml','name = "Toy"\n');self.write('lean-toolchain','toy\n')
        self.write(prepare.POLICY_REL,'{}\n');self.write('src/P/A.lean','def a := 1\n')
        self.commit('parent'); parent_head=self.git('rev-parse','HEAD')
        old=self.base/'old';self.write_snap(old,'src/P/A.lean',(self.root/'src/P/A.lean').read_bytes())
        row={'workspace_path':'src/P/A.lean','snapshot_path':'src/P/A.lean',
             'sha256':H(old/'src/P/A.lean'),'imports':[]}
        self.old={'root':str(self.root),'head':parent_head,'order':['P.A'],'sources':{'P.A':row},
                  'lakefile_sha256':H(self.root/'lakefile.toml'),'lean_toolchain_sha256':H(self.root/'lean-toolchain')}
        self.write('src/P/A.lean','def a := 1\n-- committed parent drift\n')
        self.write('src/P/B.lean','import P.A\ndef b := a\n');self.commit('addition')
        new=self.base/'new';self.write_snap(new,'src/P/A.lean',(old/'src/P/A.lean').read_bytes())
        self.write_snap(new,'src/P/B.lean',(self.root/'src/P/B.lean').read_bytes())
        b={'workspace_path':'src/P/B.lean','snapshot_path':'src/P/B.lean',
           'sha256':H(new/'src/P/B.lean'),'imports':['P.A']}
        self.new={'root':str(self.root),'head':self.git('rev-parse','HEAD'),
                  'parent_git_commit':parent_head,'parent_source_count':1,
                  'source_basis':'HISTORICAL_PARENT','order':['P.A','P.B'],
                  'sources':{'P.A':copy.deepcopy(row),'P.B':b},
                  'lakefile_sha256':self.old['lakefile_sha256'],'lean_toolchain_sha256':self.old['lean_toolchain_sha256'],
                  'target_policy_sha256':H(self.root/prepare.POLICY_REL)}
        self.old_snap=old;self.new_snap=new
    def tearDown(self):self.tmp.cleanup()
    def git(self,*args):return subprocess.check_output(['git','-C',str(self.root),*args],text=True).strip()
    def write(self,path,text):
        p=self.root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
    def write_snap(self,root,path,data):
        p=root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    def commit(self,msg):
        self.git('add','.');self.git('-c','user.name=Toy','-c','user.email=toy@example.invalid','commit','-qm',msg)
    def check(self,old=None,new=None):
        prepare.verify_historical_sources(self.old_snap,old or self.old,self.new_snap,new or self.new)
    def test_committed_parent_drift_is_historical(self):
        self.assertNotEqual((self.root/'src/P/A.lean').read_bytes(),(self.old_snap/'src/P/A.lean').read_bytes())
        self.check()
    def test_cannot_relabel_historical_basis(self):
        n=copy.deepcopy(self.new);n['source_basis']='CURRENT'
        with self.assertRaisesRegex(ValueError,'historical parent basis'):self.check(new=n)
    def test_parent_row_or_snapshot_tampering_rejected(self):
        n=copy.deepcopy(self.new);n['sources']['P.A']['sha256']='wrong'
        with self.assertRaisesRegex(ValueError,'parent source row differs'):self.check(new=n)
        (self.old_snap/'src/P/A.lean').write_text('def a := 9\n')
        with self.assertRaisesRegex(ValueError,'snapshot source mismatch'):self.check()
    def test_wrong_pinned_parent_commit_rejected(self):
        o=copy.deepcopy(self.old);n=copy.deepcopy(self.new)
        o['head']=self.new['head'];n['parent_git_commit']=o['head']
        with self.assertRaisesRegex(ValueError,'Git source differs'):self.check(old=o,new=n)
    def test_addition_commit_must_contain_exact_blob(self):
        n=copy.deepcopy(self.new);n['head']=self.old['head']
        with self.assertRaisesRegex(ValueError,'missing/non-blob Git source'):self.check(new=n)
    def test_added_workspace_source_must_remain_identical(self):
        self.write('src/P/B.lean','def b := 7\n')
        with self.assertRaisesRegex(ValueError,'added workspace source drift'):self.check()
    def test_snapshot_parent_symlink_rejected(self):
        src=self.new_snap/'src';(src/'P').rename(src/'realP');(src/'P').symlink_to('realP',target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'snapshot parent symlink'):self.check()
    def test_added_workspace_parent_symlink_rejected(self):
        src=self.root/'src';(src/'P').rename(src/'realP');(src/'P').symlink_to('realP',target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'added workspace source symlink'):self.check()
    def test_workspace_config_symlink_rejected(self):
        p=self.root/'lakefile.toml';p.rename(self.root/'lakefile-copy.toml');p.symlink_to('lakefile-copy.toml')
        with self.assertRaisesRegex(ValueError,'workspace configuration symlink'):self.check()
    def test_config_blob_and_noncommit_rejected(self):
        with self.assertRaisesRegex(ValueError,'Git source differs'):
            prepare.verify_commit_blobs(self.root,self.old['head'],{'lakefile.toml':'wrong'})
        tree=self.git('rev-parse',self.old['head']+'^{tree}')
        with self.assertRaisesRegex(ValueError,'not a commit'):
            prepare.verify_commit_blobs(self.root,tree,{})

if __name__=='__main__':unittest.main()
