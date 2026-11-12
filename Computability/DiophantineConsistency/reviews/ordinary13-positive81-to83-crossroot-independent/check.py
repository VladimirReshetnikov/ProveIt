from pathlib import Path
from hashlib import sha256
import json,sys,tempfile,shutil,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
p=P('research/ordinary13-positive81-to83-model-draft');q=P('research/ordinary13-positive80-to81-model-draft');a=P('research/ordinary13-positive81-to83-model-gap-audit')
files=[p/'generate.py',p/'PositiveCarrier83Graph.lean.src',p/'CarrierWitnessFacts.lean.src',p/'Positive81To83Transport.lean.src',p/'README.md',p/'receipt.json',q/'generate.py',q/'PositiveSquare81Graph.lean.src',q/'Positive80To81Transport.lean.src',P('research/ordinary13-qcube-main83/candidate.json'),P('research/ordinary13-residue-first81/candidate.json'),P('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),P('research/ordinary13-natural89-r-replacement-model-draft/Natural89RReplacement.lean.src'),a/'check.py',a/'receipt.json',P('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean')]
s=[f.read_text() for f in files]
for gen,inp,out in [(files[0],files[9],files[1]),(files[6],files[10],files[7])]:
 with tempfile.TemporaryDirectory(prefix='crossroot-review-') as d:
  root=P(d)
  for f in (gen,inp):
   dest=root/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
  subprocess.run([sys.executable,'-I','-S','-B',str(gen)],cwd=root,check=True)
  assert (root/out).read_bytes()==out.read_bytes()
g83,g81=map(json.loads,s[9:11]);assert len(g83['source'])==83 and len(g81['source'])==81
assert g83['witnesses']==g81['witnesses'] and g83['witnesses'][8]=='r' and g83['fixed_numerals']==g81['fixed_numerals']
a83,a81=({row[0]:row for row in g['source']} for g in (g83,g81))
assert set(a83)-set(a81)=={'g25','g28'}
for n in a83.keys() & a81.keys():
 if n not in ('g26','Bt'):assert a83[n]==a81[n],n
def deps(rows,n):
 if isinstance(n,int):return set()
 if n not in rows:return {n}
 _,_,l,r=rows[n];return deps(rows,l)|deps(rows,r)
for n in ('A1','Fa','g72'):
 assert 'r' not in deps(a83,n) and 'r' not in deps(a81,n)
# Verify the exact first-root witness identity with P=b*t by polynomial
# normalization in Z[b,t,ell,k,tau]. The witness uses P-1 and tau-ell
# only after the theorem supplies their natural lower-bound hypotheses.
def plus(a,b,sgn=1):
 c=a.copy()
 for k,n in b.items():c[k]=c.get(k,0)+sgn*n
 return {k:n for k,n in c.items() if n}
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+i*j
 return {k:n for k,n in c.items() if n}
zero=(0,)*5;one={zero:1};b={(1,0,0,0,0):1};t={(0,1,0,0,0):1};ell={(0,0,1,0,0):1};k={(0,0,0,1,0):1};tau={(0,0,0,0,1):1}
carrier=mul(b,t);r=plus(plus(mul(k,plus(carrier,one,-1)),t),plus(tau,ell,-1))
root=plus(mul(b,plus(plus(plus(ell,k),r),mul(k,carrier),-1)),carrier,-1)
assert root==mul(b,tau)
for i,terms in {2:['theorem positive_target_root','(hP : 0<P) (ht : 0<t) (hPt : P=b*t) (htau : ell<tau)','let r := k*(P-1)+t+(tau-ell)'],3:['theorem shared83_at','theorem shared81_at','theorem nonfirst_of_sum','theorem zero81_to83','theorem zero83_to81','theorem prototype_zero_of81','def CrossRootCut','theorem sameNoZero','(hc : CrossRootCut K)','(h83 : PolynomialBridge','Positive80To81TransportDraft.native85'],8:['def image85','Natural89RReplacementDraft.up (Natural89Positive80TransportDraft.lower v)','theorem zero81_to80'],11:['theorem lift_lower','theorem zero_iff'],12:['theorem zero89_iff85']}.items():
 for n in terms:assert n in s[i],(i,n)
cut=s[3].split('def CrossRootCut',1)[1].split('theorem sameNoZero',1)[0]
assert cut.index('PositiveSquare81GraphDraft.graph')<cut.index('PositiveCarrier83GraphDraft.graph')
assert cut.count('∃ r : V, 0<r')==2 and cut.count('.first.evalRing')==2
prototype=s[3].split('theorem prototype_zero_of81',1)[1].split('/--',1)[0]
for n in ['zero81_to80','lift_lower','zero_iff p n).mpr','zero89_iff85 p n).mp']:assert n in prototype
assert 'ForcedEta' not in prototype and 'CrossRootCut' not in prototype
# Reproduce independently authored exact positive81-to-prototype residual check.
run=subprocess.run([sys.executable,'-I','-S','-B',str(files[13])],check=True,stdout=subprocess.PIPE)
assert run.stdout==files[14].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'both_graph_literal_regenerations':True,'three_common_residuals_independent_of_r':True,'target_root_identity_free_ring':True,'positive81_to_prototype_receipt_reproduced':True,'cross_root_and_parent_bridge_are_assumptions':True,'lean_executed':False,'status':'Source review only; all model cuts, source elaboration, providers and endpoint remain open.'},sort_keys=True,indent=2))
