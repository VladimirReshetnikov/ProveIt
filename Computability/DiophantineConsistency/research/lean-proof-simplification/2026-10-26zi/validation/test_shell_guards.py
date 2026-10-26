#!/usr/bin/env python3
"""Exercise only refusal paths: fake toolchain files must never be executed."""
import subprocess,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];SCRIPT=ROOT/'validation/replay_candidates.sh'
class ShellGuards(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.t=Path(self.tmp.name);self.bin=self.t/'bin';self.bin.mkdir();self.marker=self.t/'executed'
  for name in ['lean','lake']:
   p=self.bin/name;p.write_text('#!/bin/sh\nprintf invoked > '+str(self.marker)+'\nexit 99\n');p.chmod(0o755)
 def tearDown(self):self.assertFalse(self.marker.exists(),'Refusal unexpectedly executed a toolchain file');self.tmp.cleanup()
 def run_script(self,*args):return subprocess.run(['bash',str(SCRIPT),*map(str,args)],text=True,capture_output=True)
 def test_usage_refused(self):self.assertEqual(self.run_script().returncode,64)
 def test_missing_binaries_refused(self):self.assertEqual(self.run_script(self.t,self.t/'missing').returncode,69)
 def test_elan_shim_refused(self):
  p=self.bin/'lean';p.unlink();(self.bin/'elan').write_text('not executable');p.symlink_to(self.bin/'elan');(self.bin/'elan').chmod(0o755)
  r=self.run_script(self.t,self.bin);self.assertEqual(r.returncode,69);self.assertIn('elan shim',r.stderr)
 def test_source_snapshot_refused(self):
  r=self.run_script(ROOT/'sources',self.bin);self.assertEqual(r.returncode,1);self.assertIn('selected source snapshot',r.stderr)
 def test_absent_checkout_refused(self):self.assertEqual(self.run_script(self.t/'absent',self.bin).returncode,69)
 def test_unpinned_directory_refused(self):
  r=self.run_script(self.t,self.bin);self.assertEqual(r.returncode,1);self.assertIn('HEAD must equal',r.stderr)
 def test_shell_syntax(self):self.assertEqual(subprocess.run(['bash','-n',str(SCRIPT)],capture_output=True).returncode,0)
if __name__=='__main__':unittest.main()
