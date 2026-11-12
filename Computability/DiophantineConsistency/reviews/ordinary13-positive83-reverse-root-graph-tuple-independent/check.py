from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
p=P('research/ordinary13-positive83-reverse-root-model-draft')
files=[p/'Positive83ReverseRoot.lean.src',p/'Positive83CrossRoot.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-positive81-carrier-data-model-draft/Positive81ForwardCarrier.lean.src'),P('research/ordinary13-positive81-carrier-data-model-draft/Positive81ForwardCompact.lean.src'),P('research/ordinary13-positive81-carrier-data-model-draft/CompanionCarrierFacts.lean.src'),P('research/ordinary13-positive81-to83-model-draft/Positive81To83Transport.lean.src'),P('research/ordinary13-positive81-to83-model-draft/PositiveCarrier83Graph.lean.src'),P('research/ordinary13-positive80-to81-model-draft/PositiveSquare81Graph.lean.src'),P('research/ordinary13-residue-first81/candidate.json'),P('research/ordinary13-qcube-main83/candidate.json'),P('research/ordinary13-positive81-exact-main-model-draft/Positive81ExactMain.lean.src'),P('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean'),P('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src'),P('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean')]
s=[f.read_text() for f in files];a,b=map(json.loads,s[11:13]);assert [len(g['source']) for g in (a,b)]==[81,83]
assert a['witnesses']==b['witnesses']==['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma'] and a['fixed_numerals']==b['fixed_numerals']==['beta','K0','MC','MF']
ra,rb=({r[0]:r for r in g['source']} for g in (a,b));assert set(rb)-set(ra)=={'g25','g28'}
for n in ra.keys() & rb.keys():
 if n not in ('g26','Bt'):assert ra[n]==rb[n],n
for rows,source in [(ra,s[10]),(rb,s[9])]:
 for n,op,l,r in rows.values():assert f'  let {n} := {l} {op} {r}\n' in source,n
for r in [['g26','+','X','K0'],['Bt','-','g27','F']]:assert ra[r[0]]==r
for r in [['g25','*','K0','q'],['g26','+','X','g25'],['g28','*','F','q'],['Bt','-','g27','g28']]:assert rb[r[0]]==r
def deps(rows,n):
 if isinstance(n,int):return set()
 if n not in rows:return {n}
 _,_,l,r=rows[n];return deps(rows,l)|deps(rows,r)
for n in ('A1','Fa','g72'):
 assert 'r' not in deps(ra,n) and 'r' not in deps(rb,n)
for n in ['def P (p : Fin 4 → ℕ)','def Q (p : Fin 4 → ℕ)','(ι (q p v)-ι (v 1)-ι (v 2))*(ι (X p v)+ι (p 1:V))-ι (v 1)',
 '(ι (q p v)-ι (v 1)-ι (v 2))*(ι (X p v)+ι (p 1:V)*ι (q p v))-ι (v 1)*ι (q p v)']:assert n in s[5],n
for n in ['theorem first83','theorem first81_update','theorem reverse_root','PositiveCarrierDataDraft.root_data',
 'CompanionCarrierFactsDraft.reduced_companion','CompanionCarrierFactsDraft.positive_target','rw [first81_update]']:assert n in s[0],n
for n in ['theorem forward (K : ℕ)','Positive81ForwardCarrierDraft.forward_root p v hv hz hbeta hgap hX']:assert n in s[6],n
assert 'theorem bounds (J : V) (hJ : 0<J)' in s[14]
assert 'CompactSymbolicPorts.ports CompactFixedBeta.betaNat K' in s[15]
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in s[16]
cut=s[8].split('def CrossRootCut',1)[1].split('theorem sameNoZero',1)[0]
assert cut.index('PositiveSquare81GraphDraft.graph')<cut.index('PositiveCarrier83GraphDraft.graph') and cut.count('∃ r : V, 0<r')==2
for n in ['theorem reverse (K : ℕ)','Positive83ReverseRootDraft.reverse_root (ports K) v hv hz hbeta','theorem crossRootCut (K : ℕ)',
 'Positive81ForwardCompactDraft.forward K v hv hz','exact reverse K V v hv hz',
 '(h83 : PolynomialBridge (positiveShift (PositiveCarrier83GraphDraft.graph',
 'Positive81To83TransportDraft.native85 K (crossRootCut K) h83']:assert n in s[1],n
# Exact symbolic identity for 83 target Q minus 81 target P, using q=1+b.
def add(x,y,sign=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sign*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
one={(0,)*5:1};b0={(1,0,0,0,0):1};F={(0,1,0,0,0):1};alpha={(0,0,1,0,0):1};X={(0,0,0,1,0):1};K={(0,0,0,0,1):1}
q=add(one,b0);C=add(add(q,F,-1),alpha,-1);P0=add(mul(C,add(X,K)),F,-1);Q=add(mul(C,add(X,mul(K,q))),mul(F,q),-1)
assert add(Q,P0,-1)==mul(b0,add(mul(C,K),F,-1))
# Reproduce the author's pinned receipt without treating it as a model proof.
r=subprocess.run([sys.executable,'-I','-S','-B',str(files[3])],check=True,stdout=subprocess.PIPE)
assert r.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'graph_rows_and_natural_tuple_pinned':True,'nonfirst_residuals_ignore_r':True,'carrier_relation_free_ring_identity':True,'reverse_and_forward_cut_directions_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Graph/tuple source review; signed arithmetic proof, unelaborated model providers, exact 83 parent bridge and endpoint remain open.'},sort_keys=True,indent=2))
