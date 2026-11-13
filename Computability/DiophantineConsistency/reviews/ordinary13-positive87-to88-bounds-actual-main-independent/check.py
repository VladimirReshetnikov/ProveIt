from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-positive87-to88-bounds-model-draft');a=P('research/ordinary13-positive87-to88-aux-model-draft')
files=[p/'Positive87To88Bounds.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',a/'Positive87To88Aux.lean.src',P('research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale87Graph.lean.src'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareGraph.lean'),P('research/ordinary13-aux-root87-36/candidate.json'),P('research/ordinary13-four-square88-30/candidate.json'),P('research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean'),P('research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean'),P('research/ordinary14-aux-root-model-draft/AuxRootBridge.lean'),P('Lean/DiophantineConsistency/Compact44/P72Root.lean')]
s=[f.read_text() for f in files];g87,g88=map(json.loads,s[8:10]);assert [len(g['source']) for g in (g87,g88)]==[87,88]
for g,src in ((g87,s[6]),(g88,s[7])):
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in src,n
r87,r88=({r[0]:r for r in g['source']} for g in (g87,g88))
for n in ('qm','q','q2','q3','M','ell','A0','U','E','H','Delta','R','r0','g54','g55','g56','shift','Dstar','A1','Q','I','g72','V'):
 assert r87[n]==r88[n],n
for row in [['M','*','q3','qm'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g71','*','I','I'],['g72','-','g71','Q'],['V','-','g76','c']]:assert r87[row[0]]==row
for n in ['def scaleFirst','qn p v*(qn p v*qn p v)*b p v','def scaleMain','v 7*(qn p v*qn p v)',
 'def rootMain','ι (v 6)*ι (v 7)*ι (qn p v)-ι (kk v)+rank (portsInt p) v+1',
 'theorem first_form','theorem main_form','theorem strong_form','theorem common_zero',
 'root_of_scaled_ring_square (scaleFirst p v)','root_of_scaled_ring_square (scaleMain p v)',
 'strong_norm_of_ring_residual','aux_bounds_of_natural_norms','def PositiveBeta','theorem bounds_cut']:
 assert n in s[0],n
for n in ['def BoundsCut','InternalZero (PositiveUnscale87GraphDraft.graph p).output v ∨','InternalZero (P88FourSquare.graph p).output v','1<Q v ∧ 1<z p v*z p v']:assert n in s[5],n
for n in ['theorem aux_bounds_of_natural_norms','(hfirst :','(hmain :','(hstrong :','(hQ :','(hz :']:assert n in s[11],n
assert 'theorem root_of_scaled_ring_square' in s[10] and 'theorem strong_norm_of_ring_residual' in s[10]
# In the free ring, literal main shift Uγ + E q - ((k-R)-1)
# is Uγ+Eq-k+R+1. Omitting Eq changes it by Eq.
def add(x,y,sgn=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sgn*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
one={(0,)*7:1};U={(1,0,0,0,0,0,0):1};gamma={(0,1,0,0,0,0,0):1};E={(0,0,1,0,0,0,0):1};q={(0,0,0,1,0,0,0):1};k={(0,0,0,0,1,0,0):1};R={(0,0,0,0,0,1,0):1};c={(0,0,0,0,0,0,1):1}
literal=add(add(mul(U,gamma),mul(E,q)),add(add(k,R,-1),one,-1),-1)
claimed=add(add(add(add(mul(U,gamma),mul(E,q)),k,-1),R),one)
assert literal==claimed
no_extra=add(add(add(mul(U,gamma),k,-1),R),one)
assert add(literal,no_extra,-1)==mul(E,q) and mul(E,q)
# V+c=f²*(T*c-R) is exact for a signed V.
f={(1,0,0,0,0,0,0):1};T={(0,1,0,0,0,0,0):1};z=add(mul(mul(f,f),add(mul(T,c),R,-1)),c,-1)
assert add(z,c)==mul(mul(f,f),add(mul(T,c),R,-1))
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'both_literal_graph_rows_and_common_norms_checked':True,'extra_XYq_shift_and_signed_aux_identity_exact':True,'scaled_root_and_strict_bound_source_interfaces_checked':True,'positive_beta_is_explicit':True,'author_receipt_reproduced':True,'lean_executed':False,'status':'Source-level review only; imported model proofs, provider replay, compact beta client and endpoint remain open.'},sort_keys=True,indent=2))
