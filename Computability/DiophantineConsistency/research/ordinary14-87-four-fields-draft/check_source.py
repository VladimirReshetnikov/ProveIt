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
for field in ('A0','A1','Fa','g72'):assert shape(old,field)==shape(new,field),field
assert shape(old,'guard')!=shape(new,'guard')
s=(P/'FourFields87.lean').read_text()
for t in ('shared_fields','fields_of_zero','fiveSquares_eq_zero_iff','P87ShiftedGuard.output_shape'):assert t in s
assert 'InternalZero (P86ResidueGraph.graph p).output v' not in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
p=D/'research/ordinary14-87-first-quotient-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
print(json.dumps({'scope':'exact four-field DAG comparison, distinct guards and own-zero source inspection; no Lean','source_sha256':hashlib.sha256((P/'FourFields87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
