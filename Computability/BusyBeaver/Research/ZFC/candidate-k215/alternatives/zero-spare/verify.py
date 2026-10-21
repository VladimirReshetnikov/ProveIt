#!/usr/bin/env python3
"""Portable quick checks; not a rerun of the full symbolic theorem executor."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
def run(script,*args):
 r=subprocess.run([sys.executable,'-B',str(ROOT/script),*map(str,args)],cwd=ROOT,text=True,capture_output=True)
 if r.returncode:raise RuntimeError(script+'\n'+r.stdout+'\n'+r.stderr)
 return r.stdout
def manifest():
 m=json.loads((ROOT/'MANIFEST.json').read_text())
 for name,pin in m['files'].items():
  raw=(ROOT/name).read_bytes();assert len(raw)==pin['size'],name
  assert hashlib.sha256(raw).hexdigest()==pin['sha256'],name
 return len(m['files'])
def main():
 n=manifest()
 with tempfile.TemporaryDirectory(prefix='z215-audit-') as name:
  t=Path(name);run('reconstruct.py','--out',t/'machine')
  for fn in ('z215.native.tm','z215.tm','sites215.json','canonicalization.json'):assert (t/'machine'/fn).read_bytes()==(ROOT/'machine'/fn).read_bytes(),fn
  for fn in ('runtime.json','runtime_cases.json.gz','startup.json.gz'):shutil.copyfile(ROOT/'verification'/fn,t/'machine'/fn)
  run('code/review_zero_spare.py',t/'machine')
  for fn in ('z215.tm','canonicalization.json'):assert (t/'machine'/fn).read_bytes()==(ROOT/'machine'/fn).read_bytes(),fn
  assert (t/'machine/independent_review.json').read_bytes()==(ROOT/'verification/independent_review.json').read_bytes()
  run('proof/check_schedule.py','--output',t/'schedule.json')
  assert (t/'schedule.json').read_bytes()==(ROOT/'proof/schedule_certificate.json').read_bytes()
  assert json.loads(run('proof/check_protected_tail_base.py'))==json.loads((ROOT/'proof/protected_tail_independent_check.json').read_text())
  run('proof/review_schedule_source.py','--source',ROOT/'machine/sites215.json','--out',t/'focused.json')
  assert (t/'focused.json').read_bytes()==(ROOT/'proof/focused_review_receipt.json').read_bytes()
  assert json.loads(run('research/alias_free/check_alias_free_ikp.py'))==json.loads((ROOT/'research/alias_free/alias_free_ikp_check.json').read_text())
  run('code/make_machine_table.py','--output',t/'machine_table.tex')
  assert (t/'machine_table.tex').read_bytes()==(ROOT/'machine_table.tex').read_bytes()
  family=json.loads(run('research/command_family/verify.py'));assert family['status']=='PASS'
 assert manifest()==n
 print(json.dumps(dict(status='PASS',manifest_files=n,primary='Exact reconstruction; native/dense full blank trace; complete terminal tape; all 6176 saved cases and positive durations.',schedule='Independent finite-base and literal source checks; all-natural extension proved in report.',alias_free='22 explicit-substitution nodes; I, K, Peirce only.',secondary=family,scope='Ordinary mathematical verification. Run replay_runtime.py for fresh symbolic derivations; no proof-assistant-kernel endpoint.'),indent=2))
if __name__=='__main__':main()
