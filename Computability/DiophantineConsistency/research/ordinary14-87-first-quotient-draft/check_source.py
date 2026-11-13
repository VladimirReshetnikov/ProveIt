#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
old=json.loads((D/'research/ordinary14-shifted-guard87-probe/candidate.json').read_bytes());new=json.loads((D/'research/ordinary14-residue-guard86/candidate.json').read_bytes())
def shape(g,t):
 rows={a:(op,x,y) for a,op,x,y in g['source']}
 def go(v):
  if v not in rows:return ('leaf',v)
  op,x,y=rows[v];return (op,go(x),go(y))
 return go(t)
assert shape(old,'A0')==shape(new,'A0')
s=(P/'FirstQuotient87.lean').read_text()
for t in ('shared_first','first_of_zero','P87ShiftedGuard.graph p','first_eval p beta v hport','QCubeQuotientFactsDraft.quotient_and_root'):assert t in s
assert 'InternalZero (P86ResidueGraph.graph p).output v' not in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-87-guard-gap-draft','ordinary14-86-first-fields-draft','ordinary14-85-86-quotient-facts-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'FirstQuotient87.lean',D/'research/ordinary14-86-first-fields-draft/FirstFields86.lean',D/'research/ordinary14-85-86-quotient-facts-draft/QuotientFacts.lean']
print(json.dumps({'scope':'source inventory, first-field DAG comparison and draft receipt replays; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
