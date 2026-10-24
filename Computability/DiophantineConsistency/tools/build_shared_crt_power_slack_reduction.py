#!/usr/bin/env python3
"""Delete both redundant Pell lower-bound slacks, retaining fixed W and the beta majorant."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/shared-crt-fixed-power-bound'
DEST=ROOT/'candidates/shared-crt-power-slack-reduction'
PINS={
 'build_equation.py':'c286c29e71678c905a9cc6c9628e7c0ffe10f994e0f29078c3d4c6e595ae9468',
 'direct_calculus.py':'68200f7a6a063c4ef8c3c1462f104f0e1f5b99e43f9fccb3db991ca1e80b9348',
 'wire_eliminated_source.json':'1e7cf2f3ea9397e138c7543d47ccd00a967b8fbb2fd4c8d58f176c409033c1bb',
 'affine_shared_step.json':'c858ecd4f87f06e16d9f7b075ccdfe911af22d928e722a470ca292ec731fdc03',
 'check_equation.py':'c9580e6d67bc5f10370fc2847d2064e6df14bae8a95979beb62236c3b70d43c4',
 'audit_power_graph.py':'762fe526a51ed2a13508cf8351fbffd81f81d68541bc0977c2f38e66f0cf76de',
 'audit_calculus.py':'86a43d8499845070c24251f69f75af9e5292350173e6d53ee38c2ebbfadd49eb'}


def need(ok,text):
 if not ok:raise RuntimeError(text)


def sha(raw):return sha256(raw).hexdigest()


def patch(name,text):
 changes=[]
 if name=='build_equation.py':
  changes=[
   ('        a2, yk, b2 = [self.new(tag + ".slack." + s) for s in ("a2", "yk", "b2")]\n',
    '        yk = self.new(tag + ".slack.yk")\n'),
   ('        self.eq(A, self.add(a2, TWO), tag + ".A_at_least_two", e2)\n',''),
   ('        self.eq(B, self.add(b2, TWO), tag + ".B_at_least_two", e2)\n',''),
   ('    H = b.sum([ep, fp, t])  # No local factorial cancellation is needed.\n',
    '    H = b.sum([ep, fp])  # Literal beta square and endpoint imply H>=t.\n')]
 elif name=='check_equation.py':
  changes=[('                "pow0.slack.a2": z["A"] - 2,\n',''),
           ('                "pow0.slack.b2": z["B"] - 2,\n','')]
 elif name=='audit_power_graph.py':
  changes=[
   ('compare all 15 remaining\n','compare all 13 remaining\n'),
   ("        'A_at_least_two': A-named('slack.a2')-2,\n",''),
   ("        'B_at_least_two': B-named('slack.b2')-2,\n",''),
   ("    require(local_certificates == 24, 'fixed-bound positive certificate variable count')\n",
    "    require(local_certificates == 22, 'redundant-lower-bound-free certificate variable count')\n")]
 for before,after in changes:
  need(text.count(before)==1,'unique '+name+' patch')
  text=text.replace(before,after)
 return text,changes


def generate(home):
 source=home/'source';source.mkdir(parents=True,exist_ok=True)
 records={}
 for name,pin in PINS.items():
  raw=(PARENT/'source'/name).read_bytes();need(sha(raw)==pin,'frozen fixed-bound parent source pin')
  text,changes=patch(name,raw.decode());child=text.encode();(source/name).write_bytes(child)
  records[name]=dict(parent_sha256=pin,candidate_sha256=sha(child),exact_replacements=changes)
 (home/'LICENSE.upstream').write_bytes((PARENT/'LICENSE.upstream').read_bytes())
 copies={
  'FIXED_BOUND_PROOF.md':PARENT/'PROOF.md',
  'PRIME_LIFT_PROOF.md':ROOT/'candidates/shared-crt-prime-lift/PROOF.md',
  'BETA_MAJORANT_PROOF.md':ROOT/'candidates/shared-crt-beta-majorant/PROOF.md',
  'majorant_audit.py':ROOT/'candidates/shared-crt-beta-majorant/majorant_audit.py'}
 copied={}
 for name,path in copies.items():
  raw=path.read_bytes();(home/name).write_bytes(raw);copied[name]=dict(source=str(path.relative_to(ROOT)),sha256=sha(raw))
 (home/'SOURCE_PINS.json').write_text(json.dumps(dict(parent='candidates/shared-crt-fixed-power-bound',files=records,copied_files=copied,
  semantic_changes=['Inherited fixed W=n+k.','Delete A>=2 and B>=2 slacks/rows: positivity of T and the retained norm/congruence rows force both.','Replace H=E+F+t by literal E+F; actual beta square plus endpoint supplies H>=t.']),indent=2)+'\n')
 for folder,flags in [('affine',[]),('retained',['--keep-linear-wires'])]:
  p=subprocess.run([sys.executable,'-B',str(source/'build_equation.py'),*flags,'--output',str(home/folder)],capture_output=True,text=True)
  need(p.returncode==0,'literal build: '+p.stderr)


def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 if args.check:
  with tempfile.TemporaryDirectory(prefix='proveit-power-slack-reduction-')as tmp:
   fresh=Path(tmp);generate(fresh)
   for path in fresh.rglob('*'):
    if path.is_file()and '__pycache__'not in path.parts:
     need((DEST/path.relative_to(fresh)).read_bytes()==path.read_bytes(),'deterministic '+str(path.relative_to(fresh)))
 else:
  DEST.mkdir(exist_ok=True);generate(DEST)
 print(json.dumps(dict(status='PASS',check=args.check,variants={v:json.loads((DEST/v/'BUILD.json').read_text())['metrics']for v in ['affine','retained']}),indent=2))


if __name__=='__main__':main()
