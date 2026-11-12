#!/usr/bin/env python3
"""Four exact first-root dependencies and ring identities; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path;return b
files={
 'ordinary13-natural-residue-forced89-degree56':'c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a',
 'ordinary13-natural-residue-forced88-degree60':'cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2',
 'ordinary13-natural-residue-eta-fold88-degree56':'f71cb18bdc28088a7a7c7c7ae84afc15e49470ee3d4fa4076d8c25d6d2b89b58',
 'ordinary13-natural-residue-eta-fold87-degree60':'81a09c0504bc786afb017483225e1fb6b1a52e9ddd98f53b0643dfb23c3a602f'}
for path,h in files.items():
 g=json.loads(pin('research/'+path+'/candidate.json',h));rows={r[0]:r for r in g['source']}
 for r in [['g31','+','g30','n_r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Fam','-','Fa',1],['Fam2','*','Fam','Fam'],['Fsm2','*','g72','g72'],['sum01','+','A0sq','A1sq'],['sum23','+','Fam2','Fsm2'],['out','+','sum01','sum23']]:assert rows[r[0]]==r,(path,r)
 assert sum('n_r' in r[2:] for r in g['source'])==1
 def deps(target):
  todo=[target];seen=set(todo)
  while todo:
   node=todo.pop()
   for x in rows.get(node,[None,None,None,None])[2:]:
    if isinstance(x,str) and x not in seen:seen.add(x);todo.append(x)
  return seen
 for node in ('A1','Fam','g72','Bt','qm','ell','k'):assert 'n_r' not in deps(node),(path,node)
 assert 'n_r' in deps('A0')
# Free polynomial difference of squared first roots under r := 2*tau.
def var(n):return {(n,):1}
def con(n):return {():n} if n else {}
def add(a,b,s=1):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for x,u in a.items():
  for y,v in b.items():
   m=tuple(sorted(x+y));z[m]=z.get(m,0)+u*v
 return {k:v for k,v in z.items() if v}
b,ell,k,B,tau=map(var,['b','ell','k','B','tau']);Z0=add(mul(b,add(add(ell,k),mul(k,B),-1)),B,-1)
Znew=add(Z0,mul(con(2),mul(b,tau)))
assert add(mul(Znew,Znew),mul(Z0,Z0),-1)==mul(mul(con(4),mul(b,tau)),add(Z0,mul(b,tau)))
N=add(con(1),mul(ell,add(ell,k)))
assert add(N,mul(ell,ell),-1)==add(con(1),mul(ell,k))
assert add(mul(add(ell,k),add(ell,k)),N,-1)==add(add(mul(ell,k),mul(k,k)),con(1),-1)
q=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884').decode()
m=pin('Lean/DiophantineConsistency/ModelRelationCombining.lean','559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6').decode()
d=pin('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
assert 'theorem scaled_quotient (m z n : V)' in q and 'theorem sq_dvd_sq (m s : DiffRing V)' in m and 'theorem nonneg_iff' in d and 'theorem one_le_of_pos' in d
print(json.dumps({'scope':'four pinned graph dependencies and exact ring identities; root-switch/model proof still an obligation','graphs':{k:len(json.loads(pin('research/'+k+'/candidate.json',v))['source']) for k,v in files.items()},'only_first_residual_depends_on_r':True,'root_square_difference_identity':True,'pell_strict_bound_identities':True,'signed_square_divisibility_source_pinned':True,'lean_elaboration':False},sort_keys=True,indent=2))
