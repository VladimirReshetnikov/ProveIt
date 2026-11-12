from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
files=[P('research/ordinary13-residue-first81/candidate.json'),P('research/ordinary13-qcube-main83/candidate.json'),P('research/ordinary13-unit-product80/candidate.json'),P('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),P('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),P('research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src'),P('research/ordinary13-eta-natural-parity-boundary-draft/EtaNaturalParityBoundary.lean.src'),P('research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src'),P('research/ordinary13-eta-zero-direct-projection-model-draft/EtaZeroDirectProjection.lean.src'),P('Lean/DiophantineConsistency/Compact44/P72Exact.lean'),P('research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src'),P('research/ordinary13-residue82-model-transfer-audit/README.md'),P('research/ordinary13-residue-first81/README.md')]
s=[f.read_text() for f in files];a,b,c,d=map(json.loads,s[:4]);
assert [len(g['source']) for g in (a,b,c,d)]==[81,83,80,85]
assert a['witnesses']==b['witnesses']==c['witnesses'] and d['witnesses']==['n_'+x for x in a['witnesses']]
ra,rb,rc=({r[0]:r for r in g['source']} for g in (a,b,c))
for n in ra.keys() & rc.keys():
 if n not in ('out',): assert ra[n]==rc[n],n
assert set(rb)-set(ra)=={'g25','g28'}
for n in ra.keys() & rb.keys():
 if n not in ('g26','Bt'): assert ra[n]==rb[n],n
assert ra['g26']==['g26','+','X','K0'] and rb['g26']==['g26','+','X','g25']
assert ra['Bt']==['Bt','-','g27','F'] and rb['Bt']==['Bt','-','g27','g28']
# Canonical additive normal forms with opaque commutative products. This
# compares four exact residual expressions without expanding large powers.
vec=[];vid={};atoms={}
def v(d):
 z=tuple(sorted((a,b) for a,b in d.items() if b))
 if z not in vid:vid[z]=len(vec);vec.append(z)
 return vid[z]
def atom(k):
 if k not in atoms:atoms[k]=len(atoms)+1
 return atoms[k]
def var(n):return v({atom(('v',n)):1})
def num(n):return v({0:n})
def add(x,y,sign=1):
 z=dict(vec[x])
 for k,n in vec[y]:z[k]=z.get(k,0)+sign*n
 return v(z)
def mul(x,y):
 if not vec[x] or not vec[y]:return num(0)
 if len(vec[x])==1 and vec[x][0][0]==0:return v({k:vec[x][0][1]*n for k,n in vec[y]})
 if len(vec[y])==1 and vec[y][0][0]==0:return mul(y,x)
 return v({atom(('m',*sorted((x,y)))):1})
def evaluate(g,e):
 e=e.copy()
 for n,op,x,y in g['source']:
  x=num(x) if isinstance(x,int) else e[x];y=num(y) if isinstance(y,int) else e[y]
  e[n]={'+':lambda:add(x,y),'-':lambda:add(x,y,-1),'*':lambda:mul(x,y)}[op]()
 return e
vals={w:var(w) for w in a['witnesses']};ports={w:var(w) for w in a['fixed_numerals']};raw=evaluate(a,{**vals,**ports})
# 81 positive -> 89 lower (ten coordinates), then J/gamma/w/eta raises.
subtracted={1,2,4,5,7,10}
e85={'n_'+w:(add(vals[w],num(1),-1) if i in subtracted else vals[w]) for i,w in enumerate(a['witnesses'])}
res=evaluate(d,{**e85,**ports})
for name in ('A0','A1','Fa','g72','q','X','Y','R','k','c','Delta','Z'):assert raw[name]==res[name],name
# Small scalar control has a zero companion carrier but is not a graph zero.
beta,J,F,alpha,K0,X,MC,MF=46,1,1,45,0,47,1,1
q=1+J*beta;C=q-F-alpha;bp=C*(X+K0)-F;B=C*(X+K0*q)-F*q
R=(alpha+(q-F)*(q-1))*(q*q-1)+(MC+q*MF)*J
assert (q,C,bp,B,R)==(47,1,46,0,4771536)
assert X==q and X<q*q and R>=q**3 and R+q**3+q+1<=q**4
for i,needle in [(4,'theorem compact_early_index'),(5,'theorem ordinary_strong'),(6,'theorem'),(7,'theorem power'),(8,'theorem power_of_direct_carrier'),(9,'theorem indices_ordinary'),(10,'theorem compact_rank_window')]:assert needle in s[i]
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'exact_81_83_carrier_row_difference':True,'exact_positive81_to_eta85_residual_identity':True,'positive81_to_eta85_subtracted_positions':sorted(subtracted),'scalar_control_q':q,'scalar_control_B':B,'scalar_control_is_full_zero':False,'lean_executed':False,'status':'Source and scalar gap audit; no model proof, graph map, endpoint or physical file binding.'},sort_keys=True,indent=2))
