#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'Growth85.lean').read_text()
for t in ('Divides3X85Draft.divides_three_X','Arithmetic.le_of_dvd','(hbeta46 : 46≤beta)','P72ExactIndices85Draft.exact_indices','power_bound xx yy r kk cc','Exp.exp (naturalRank beta MC MF v)<Y beta v'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for X in range(1,100):
 if 47<=3*X:assert 16<=X
for n in range(13,100):
 r=n-1;R=2*n-1;assert r>=2 and R==2*r+1
p=D/'research/ordinary14-85-divides-3x-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'Growth85.lean',p/'Divides3X85.lean',D/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean',D/'Lean/DiophantineConsistency/Compact44/FreeJPowerGrowth.lean']
print(json.dumps({'scope':'source interface inventory, finite threshold/index controls and draft receipt replay; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
