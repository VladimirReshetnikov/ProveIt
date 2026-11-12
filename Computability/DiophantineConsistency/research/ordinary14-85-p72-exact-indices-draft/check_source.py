#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'P72ExactIndices85.lean').read_text()
for t in ('P72FirstInputs85Draft.first_inputs','MainIndex85Draft.main_index','DirectNorms85Draft.strong_norm','AuxNorm85Draft.aux_norm','P72Exact.indices_ordinary','hR26 hny hks hRwindow hnmod hy hnorm hstrong haux','hMC : MC<beta','hMF : MF<2*beta','m=R ∧ 2*n=R+1'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for a in range(100):assert (a+1)*(a+3)==3+4*a+a*a
for name in ('ordinary14-85-p72-first-inputs-draft','ordinary14-85-main-index-draft','ordinary14-85-direct-norms-draft','ordinary14-85-aux-norm-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'P72ExactIndices85.lean',D/'research/ordinary14-85-p72-first-inputs-draft/P72FirstInputs85.lean',D/'research/ordinary14-85-main-index-draft/MainIndex85.lean',D/'research/ordinary14-85-direct-norms-draft/DirectNorms85.lean',D/'research/ordinary14-85-aux-norm-draft/AuxNorm85.lean',D/'Lean/DiophantineConsistency/Compact44/P72Exact.lean']
print(json.dumps({'scope':'source/interface inventory, delta controls and four draft receipt replays; no Lean invocation','delta_controls':100,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
