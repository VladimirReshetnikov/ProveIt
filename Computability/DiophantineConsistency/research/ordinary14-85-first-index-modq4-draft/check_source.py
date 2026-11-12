#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'FirstIndexModQ485.lean').read_text()
for t in ('first_index_residues','Q4Rank85Draft.q4_rank','magnitude_mod','mod_add_remove_left_of_dvd','(2*n)%(q^4)=(R+1)%(q^4)','q^4∣4*Q*s'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840110)
for _ in range(200):
 q=rng.randint(1,12);X=rng.randint(1,7);ss=rng.randint(1,7);Y=q**3*ss;Q=X*Y*Y;n=rng.randint(1,8);s0=rng.randint(0,8);k=2*n+4*Q*s0;R=k-1+q**4*rng.randint(0,7)
 assert (4*Q*s0)%q**4==0 and abs(R+1-k)%q**4==0 and (2*n)%q**4==(R+1)%q**4
for name in ('ordinary14-85-first-index-residues-draft','ordinary14-85-q4-rank-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'FirstIndexModQ485.lean',D/'research/ordinary14-85-first-index-residues-draft/FirstIndexResidues85.lean',D/'research/ordinary14-85-q4-rank-draft/Q4Rank85.lean',D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean']
print(json.dumps({'scope':'source inventory, finite congruence controls and two draft receipt replays; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
