#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-first-cut-retry01';O=D/'research/nine-sharing-sign27-first-cut-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'b75ec37d48d49cff2bc920a28bc8ce4761eb4e113344d88af1dc9947cdf5b930','source-manifest.json':'c1655d2f683b77afae93a5cab8681936323a5b50c6243bcd0f53c80f818e93c4','sign28-survey.py':'eda25e29ad5397a980627ebfc04687b5b2b07a0adb7ce5ef3788b5e4ae0bfeff','src/DiophantineConsistency/Sign27FirstCut.lean':'edf59a6e7590fa6f7940f86c597ff1eb21f5acb3337fb89a0c6b5aa2add296a1'}.items():assert H(P/n)==h
old=(O/'src/DiophantineConsistency/Sign27FirstCut.lean').read_text(); new=(P/'src/DiophantineConsistency/Sign27FirstCut.lean').read_text(); a='Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul]';b='Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]';assert old.count(a)==1 and old.replace(a,b)==new
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.SharingSign27Squares','DiophantineConsistency.SharingSign28Squares']
f=D/'reviews/nine-sharing-sign27-first-cut-failure-frontier-independent/check.py';assert H(f)=='6f54d443613e753b8c63a78b88f57dda6a7aedf528e3326de94e820b8753054d';subprocess.run([sys.executable,'-I','-S','-B',str(f)],capture_output=True,text=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'same lift, deleted N1 row/zero and first residual; proof-only numeral cast normalization; no Lean replay'},sort_keys=True,indent=2))
