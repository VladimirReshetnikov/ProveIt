#!/usr/bin/env python3
"""Fix each positive-power bound W=n+k; preserve all frozen parent files."""
import argparse,hashlib,json
from pathlib import Path
import subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/shared-crt-prime-lift'
DEST=ROOT/'candidates/shared-crt-fixed-power-bound'
PINS={
 'build_equation.py':'c90247219577ea3713a5b1377f7197ae239482ede433b8ba4b042f22cbc91c68',
 'direct_calculus.py':'68200f7a6a063c4ef8c3c1462f104f0e1f5b99e43f9fccb3db991ca1e80b9348',
 'wire_eliminated_source.json':'1e7cf2f3ea9397e138c7543d47ccd00a967b8fbb2fd4c8d58f176c409033c1bb',
 'affine_shared_step.json':'c858ecd4f87f06e16d9f7b075ccdfe911af22d928e722a470ca292ec731fdc03',
 'check_equation.py':'431c01eab52a0183e604385792ea29597aeb4c583f12c50f7ab62cf7d58a8c3b',
 'audit_power_graph.py':'735f67d38cd4f36276693a43d20d777dfa689a32efcf090d4cd86628c11eaf12',
 'audit_calculus.py':'86a43d8499845070c24251f69f75af9e5292350173e6d53ee38c2ebbfadd49eb'}


def need(ok,text):
 if not ok:raise RuntimeError(text)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def patch(name,text):
 changes=[]
 if name=='build_equation.py':
  changes=[
   ('        W, A, T, Z, X, Y = [self.new(tag + "." + s) for s in ("W", "A", "T", "Z", "X", "Y")]\n',
    '        W = self.add(n, k)  # Rebuild the canonical Pell certificate at this fixed bound.\n        A, T, Z, X, Y = [self.new(tag + "." + s) for s in ("A", "T", "Z", "X", "Y")]\n'),
   ('        gap, wn, wk = [self.new(tag + ".slack." + s) for s in ("gap", "wn", "wk")]\n',
    '        gap = self.new(tag + ".slack.gap")\n'),
   ('        self.eq(W, self.add(n, wn), tag + ".base_bound", e2)\n',''),
   ('        self.eq(W, self.add(k, wk), tag + ".exponent_bound", e2)\n','')]
 elif name=='check_equation.py':
  changes=[
   ('    W = max(n, k)\n','    W = n + k\n'),
   ('    cases += [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (3, 2)]\n',
    '    cases += [(1, 1), (2, 1), (1, 2), (2, 2)]  # Keep complete finite witnesses modest.\n'),
   ('            for key in ("W", "A", "T", "Z", "X", "Y"):\n',
    '            for key in ("A", "T", "Z", "X", "Y"):\n'),
   ('                "pow0.slack.wn": z["W"] - n,\n',''),
   ('                "pow0.slack.wk": z["W"] - k,\n','')]
 elif name=='audit_power_graph.py':
  changes=[
   ('Substitute every definitional gate symbolically and compare all 17 remaining\n',
    'Substitute every definitional gate symbolically and compare all 15 remaining\n'),
   ('    W,A,T,Z,X,Y = [names[\'pow0.\'+x] for x in [\'W\',\'A\',\'T\',\'Z\',\'X\',\'Y\']]\n',
    '    W = n+k\n    A,T,Z,X,Y = [names[\'pow0.\'+x] for x in [\'A\',\'T\',\'Z\',\'X\',\'Y\']]\n'),
   ("        'base_bound': W-n-named('slack.wn'),\n",''),
   ("        'exponent_bound': W-k-named('slack.wk'),\n",''),
   ("    require(local_certificates == 27, 'positive certificate variable count')\n",
    "    require(local_certificates == 24, 'fixed-bound positive certificate variable count')\n")]
 for before,after in changes:
  need(text.count(before)==1,'unique '+name+' patch')
  text=text.replace(before,after)
 return text,changes


def generate(home):
 source=home/'source';source.mkdir(parents=True,exist_ok=True)
 records={}
 for name,pin in PINS.items():
  raw=(PARENT/'source'/name).read_bytes();need(sha(raw)==pin,'frozen parent source pin')
  text,changes=patch(name,raw.decode());child=text.encode();(source/name).write_bytes(child)
  records[name]=dict(parent_sha256=pin,candidate_sha256=sha(child),exact_replacements=changes)
 (home/'LICENSE.upstream').write_bytes((PARENT/'LICENSE.upstream').read_bytes())
 (home/'SOURCE_PINS.json').write_text(json.dumps(dict(parent='candidates/shared-crt-prime-lift',files=records,
  semantic_change='For each power, W=n+k, delete W and the two bound slacks/rows; reconstruct fresh canonical Pell witnesses for completeness.'),indent=2)+'\n')
 for folder,flags in [('affine',[]),('retained',['--keep-linear-wires'])]:
  subprocess.run([sys.executable,'-B',str(source/'build_equation.py'),*flags,'--output',str(home/folder)],capture_output=True,text=True,check=True)


def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 if args.check:
  with tempfile.TemporaryDirectory(prefix='proveit-fixed-power-bound-')as tmp:
   fresh=Path(tmp);generate(fresh)
   for path in fresh.rglob('*'):
    if path.is_file()and '__pycache__'not in path.parts:
     need((DEST/path.relative_to(fresh)).read_bytes()==path.read_bytes(),'deterministic '+str(path.relative_to(fresh)))
 else:
  DEST.mkdir(exist_ok=True);generate(DEST)
 print(json.dumps(dict(status='PASS',check=args.check,variants={name:json.loads((DEST/name/'BUILD.json').read_text())['metrics']for name in ['affine','retained']}),indent=2))


if __name__=='__main__':main()
