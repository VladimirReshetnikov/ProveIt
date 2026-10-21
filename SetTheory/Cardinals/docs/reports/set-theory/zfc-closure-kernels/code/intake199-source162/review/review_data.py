#!/usr/bin/env python3
"""Own inert literal tables / printed table / finite matrix reader. No imports from delivery."""
from pathlib import Path
from itertools import product
import json,re,hashlib
P=Path(__file__).resolve().parent;D=P/'extracted/K215_Composed_Selector_2026-10-20';K=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 out={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();out[int(q),int(b)]=(int(w),d,int(z))
 return out
T=table(D/'machine/k215.native.tm');C=table(D/'machine/k215.tm');old=table(K/'candidate-k216/k216.native.tm');printed={}
for l in(D/'sections/full_table.tex').read_text().splitlines():
 if re.match(r'^\d+ &',l):
  vals=re.findall(r'(\d+) & \\texttt\{([01])([LR])(\d+)\} & \\texttt\{([01])([LR])(\d+)\}',l)
  for q,w0,d0,z0,w1,d1,z1 in vals:printed[int(q),0]=(int(w0),d0,int(z0));printed[int(q),1]=(int(w1),d1,int(z1))
assert printed==C;changes={}
for l in(D/'sections/changed_rows.tex').read_text().splitlines():
 m=re.match(r'^(\d+) & ([01]) & \\texttt\{([01])([LR])(\d+)\} & \\texttt\{([01])([LR])(\d+)\}',l)
 if m:
  q,b,w0,d0,z0,w1,d1,z1=m.groups();k=(int(q),int(b));assert old[k]==(int(w0),d0,int(z0));assert T[k]==(int(w1),d1,int(z1));changes[k]=T[k]
assert changes=={k:T[k]for k in T if old.get(k)!=T[k]};assert len(changes)==35;assert set(q for q,b in old)-set(q for q,b in T)=={224}
matrices=[]
for x in json.loads((D/'research/logical_restrictions/countermodels.json').read_text()):
 I=lambda a,b:x['implication_table'][a][b];assert I(0,0)==0;assert all(I(0,b)!=0 for b in[1,2]);tot=0
 for a,b,c in product(range(3),repeat=3):
  u={'U=A':a,'U=B':b,'U=C':c,'U=0':0}[x['restriction']];assert I(I(I(c,u),a),I(I(a,c),I(b,c)))==0;tot+=1
 for e in x['counterexamples']:
  a,b=e['p'],e['q'];v=I(a,I(b,a))if e['theorem']=='K'else I(I(I(a,b),a),a);assert v==e['value']!=0
 matrices.append({'restriction':x['restriction'],'instances':tot,'counterexamples':len(x['counterexamples'])})
R={'status':'OWN_INERT_LITERAL_AND_MATRIX_REVIEW_PASS','printed_canonical_rows':len(printed),'printed_changed_parent_rows':len(changes),'deleted_parent_state':224,'matrices':matrices,'scope':'Printed-data consistency and explicit finite implication-only algebras; no supplied execution, TM simulation, symbolic runtime replay, full native countermodel or smaller machine.','script_sha256':sha(Path(__file__))};(P/'data-review.json').write_text(json.dumps(R,indent=2)+'\n');print(json.dumps(R,indent=2))
