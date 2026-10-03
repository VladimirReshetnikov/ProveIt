"""Independent read-only check of fixed DAG degree and symbolic top form.
No source modules from the frozen package are imported or executed.
"""
import argparse, array, hashlib, json, mmap, resource, struct, time
from pathlib import Path
from functools import lru_cache
MAX_MEMORY=512*1024**2; MAX_SECONDS=180; MAX_TERMS=4096
resource.setrlimit(resource.RLIMIT_AS,(MAX_MEMORY,MAX_MEMORY))
resource.setrlimit(resource.RLIMIT_CPU,(MAX_SECONDS,MAX_SECONDS))
started=time.monotonic()
def need(ok,message):
 if not ok:raise ValueError(message)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',required=True,help='Directory containing the three pinned frozen DAG/JSON files')
parser.add_argument('--output',type=Path,required=True,help='Explicit certificate output path outside the release')
args=parser.parse_args()
# Portable packaging adaptation: no replay result may overwrite delivered evidence.
args.output=args.output.expanduser().resolve()
_release=Path(__file__).resolve().parents[2]
if args.output == _release or _release in args.output.parents:
 raise ValueError('Output must be outside the complete release')
ROOT=Path(args.source_dir).resolve()
DEST=Path(__file__).resolve().parent
EXPECTED='a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2'
for filename,sha in [('universal.json','41e6f754df8f60448e1207ef36e6161729b52004fac719a580d6ec643d039d49'),('native_unit_kernel.json','2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae')]:
 need((hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()==sha),'Check failed: hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()==sha')
M=json.loads((ROOT/'universal.json').read_text())
KERNEL=json.loads((ROOT/'native_unit_kernel.json').read_text())
RAW=(ROOT/'universal.dag').read_bytes()
need((hashlib.sha256(RAW).hexdigest()==EXPECTED),'Check failed: hashlib.sha256(RAW).hexdigest()==EXPECTED')
need((RAW[:8]==b'CDAGv1\0\0'),"Check failed: RAW[:8]==b'CDAGv1\\0\\0'")
ROW=struct.Struct('<Bqq'); BASE=1<<50
need((M['input_base']==BASE and M['input_count']==797141),"Check failed: M['input_base']==BASE and M['input_count']==797141")
need(((len(RAW)-8)//17==3600546 and (len(RAW)-8)%17==0),'Check failed: (len(RAW)-8)//17==3600546 and (len(RAW)-8)%17==0')
inputs={v['name']:BASE+v['start'] for v in M['inputs']}
const={int(v[1]):-i-1 for i,v in enumerate(M['constants']) if v[0]=='int'}
def row(g):return ROW.unpack_from(RAW,8+17*g)
def c(h):
 r=M['constants'][-h-1];need((r[0]=='int'),r)
 return int(r[1])
# The raw final kernel is matched operand-for-operand to inert JSON.
env={n:inputs['native.'+n] for n in KERNEL['auxiliaries']}
env.update({'@H':3600206,'@M':3600215,'@Z':3600216,'@scale':3600218})
for idx,(name,op,a,b) in enumerate(KERNEL['source'],3600219):
 resolve=lambda x:const[x] if type(x)==int else env[x]
 need((row(idx)==({'+':0,'-':1,'*':2}[op],resolve(a),resolve(b))),(name,idx))
 env[name]=idx
need((env[KERNEL['unit']]==M['extra']['native_unit']),"Check failed: env[KERNEL['unit']]==M['extra']['native_unit']")
need(([env[n] for n in KERNEL['unit_factors']]==M['extra']['unit_factors']),"Check failed: [env[n] for n in KERNEL['unit_factors']]==M['extra']['unit_factors']")
# Verify the exact P expression and its degree-three homogeneous form.
P=1985724; J=1985722; SHAT=inputs['native.Shat']; COUNT=794976
need((row(310)==(0,inputs['input_loader__X'],inputs['native.Z0'])),"Check failed: row(310)==(0,inputs['input_loader__X'],inputs['native.Z0'])")
need((row(311)==(2,310,inputs['native.Vfinal'])),"Check failed: row(311)==(2,310,inputs['native.Vfinal'])")
need((row(312)==(0,311,inputs['input_loader__X'])),"Check failed: row(312)==(0,311,inputs['input_loader__X'])")
need((row(313)==(0,312,inputs['native.phase_initial'])),"Check failed: row(313)==(0,312,inputs['native.phase_initial'])")
need((row(314)==(0,313,inputs['native.height_slack'])),"Check failed: row(314)==(0,313,inputs['native.height_slack'])")
need((row(315)==(2,-36,314) and M['constants'][35]==['pow2',551890]),"Check failed: row(315)==(2,-36,314) and M['constants'][35]==['pow2',551890]")
need((row(316)==(1,315,const[1])),'Check failed: row(316)==(1,315,const[1])')
need((row(J)==(1,1985718,const[COUNT])),'Check failed: row(J)==(1,1985718,const[COUNT])')
need((row(1985723)==(2,316,J)),'Check failed: row(1985723)==(2,316,J)')
need((row(P)==(0,1985723,const[1])),'Check failed: row(P)==(0,1985723,const[1])')
# Prove that the linear leading factor J is the sum of every Shat once.
seen=bytearray(COUNT); todo=[1985718]; leaf_count=0; sum_gates=0
while todo:
 h=todo.pop()
 if h>=BASE:
  need((SHAT<=h<SHAT+COUNT),'Check failed: SHAT<=h<SHAT+COUNT')
  j=h-SHAT;need((seen[j]==0),'Check failed: seen[j]==0');seen[j]=1;leaf_count+=1
 else:
  op,a,b=row(h);need((op==0),'Check failed: op==0')
  todo.extend((a,b));sum_gates+=1
need((leaf_count==COUNT and sum_gates==COUNT-1 and all(seen)),'Check failed: leaf_count==COUNT and sum_gates==COUNT-1 and all(seen)')
# Degree upper bounds. The only special rule is the all-tuple R15 identity.
deg=array.array('Q')
def d(h):return 0 if h<0 else 1 if h>=BASE else deg[h]
a=env['and__R12']; cc=env['and__R10a']; u=env['and__wn2']; gamma=env['and__ga']; dd=env['and__a4m5']; r15=env['and__R15']
# (coefficient, ordered factors) for the exact expanded norm identity.
replacement=[(1,[u,u]),(2,[u,a,cc]),(2,[u,gamma,dd]),(2,[a,cc,gamma,dd]),(1,[gamma,gamma,dd,dd]),(-1,[dd,cc,cc])]
start=time.monotonic()
for gate in range(3600546):
 if gate%100000==0:need(time.monotonic()-started<MAX_SECONDS,'wall time limit')
 op,l,r=row(gate)
 need((op in (0,1,2)),'Check failed: op in (0,1,2)')
 need((all(h<0 and -h<=len(M['constants']) or h>=BASE and h-BASE<M['input_count'] or 0<=h<gate for h in (l,r))),"Check failed: all(h<0 and -h<=len(M['constants']) or h>=BASE and h-BASE<M['input_count'] or 0<=h<gate for h in (l,r))")
 bound=d(l)+d(r) if op==2 else max(d(l),d(r))
 if gate==r15:
  original_r15=bound
  term_degrees=[sum(d(h) for h in factors) for _,factors in replacement]
  bound=max(term_degrees)
 deg.append(bound)
need((d(P)==3 and d(3600218)==2391033),'Check failed: d(P)==3 and d(3600218)==2391033')
need((d(r15)==11955172 and d(M['output'])==69339973),"Check failed: d(r15)==11955172 and d(M['output'])==69339973")
# Sparse exact polynomials in the opaque atom p=HH_3(P) and actual input atoms.
# A monomial is sorted (atom,exponent) pairs; coefficients are arbitrary ints.
def add(A,B,sign=1):
 C=A.copy()
 for k,v in B.items():
  C[k]=C.get(k,0)+sign*v
  if C[k]==0:del C[k]
 need(len(C)<=MAX_TERMS,'sparse sum term limit')
 return C
def mul(A,B):
 need(len(A)*len(B)<=MAX_TERMS**2,'sparse product limit')
 C={}
 for aa,av in A.items():
  for bb,bv in B.items():
   powers=dict(aa)
   for k,e in bb:powers[k]=powers.get(k,0)+e
   key=tuple(sorted(powers.items()))
   C[key]=C.get(key,0)+av*bv
   need(len(C)<=MAX_TERMS,'sparse term limit')
 return {k:v for k,v in C.items() if v}
def powpoly(A,n):
 B={():1}
 while n:
  if n&1:B=mul(B,A)
  A=mul(A,A);n//=2
 return B
def var(name):return {((name,1),):1}
def scalar(k):return {():k} if k else {}
def product(factors):
 v={():1}
 for x in factors:v=mul(v,x)
 return v
@lru_cache(None)
def hh(h):
 if h==P:return var('p')
 if h<0:return scalar(c(h))
 if h>=BASE:return var('x'+str(h-BASE))
 if h==r15:
  v={}
  for (co,factors),td in zip(replacement,term_degrees):
   if td==d(h):v=add(v,product([scalar(co)]+[hh(x) for x in factors]))
  return v
 op,l,r=row(h)
 if op==2:return mul(hh(l),hh(r))
 return add(hh(l) if d(l)==d(h) else {},hh(r) if d(r)==d(h) else {},1 if op==0 else -1)
N=797011; E=29*N-8
p=var('p')
v=lambda name:var('x'+str(inputs['native.'+name]-BASE))
k=add(v('and__eta'),v('and__zeta'))
delta=add(v('and__tau_gap'),k,-1)
Z_expected=mul(powpoly(p,N-4),v('H_V'))
need((hh(3600218)==powpoly(p,N)),'Check failed: hh(3600218)==powpoly(p,N)')
need((hh(3600216)==Z_expected),'Check failed: hh(3600216)==Z_expected')
expected=product([scalar(2**138),powpoly(p,E),v('and__ga'),powpoly(v('and__w'),5),powpoly(v('and__odd_half'),15),powpoly(k,10),powpoly(v('and__f'),2),powpoly(v('and__i'),4),delta,powpoly(v('H_V'),2)])
actual=hh(M['output'])
need((actual==expected and len(actual)==23),'Check failed: actual==expected and len(actual)==23')
# Verify every emitted finalizer row and the uniquely maximal residual square.
residuals=M['extra']['residual_pairs'];squares=M['extra']['residual_squares']
for (l,r),sq in zip(residuals,squares):
 need((row(sq-1)==(1,l,r) and row(sq)==(2,sq-1,sq-1)),'Check failed: row(sq-1)==(1,l,r) and row(sq)==(2,sq-1,sq-1)')
mx=max(d(sq) for sq in squares)
need(([j for j,sq in enumerate(squares) if d(sq)==mx]==[6]),'Check failed: [j for j,sq in enumerate(squares) if d(sq)==mx]==[6]')
need((mx==19128284),'Check failed: mx==19128284')
# Explicit symbolic identity check in four independent abstract atoms.
aa,cc2,uu,gg=map(var,['a','c','u','gamma'])
ddd=add(mul(scalar(4),aa),scalar(3))
norm=add(powpoly(add(add(uu,mul(aa,cc2)),mul(gg,ddd)),2),mul(add(powpoly(aa,2),ddd),powpoly(cc2,2)),-1)
rhs=add(add(add(add(add(powpoly(uu,2),product([scalar(2),uu,aa,cc2])),product([scalar(2),uu,gg,ddd])),product([scalar(2),aa,cc2,gg,ddd])),product([gg,gg,ddd,ddd])),product([ddd,cc2,cc2]),-1)
need((norm==rhs),'Check failed: norm==rhs')
report={
 'source_sha256':EXPECTED,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'kernel_rows_matched':len(KERNEL['source']),'all_shat_inputs_checked_once':COUNT,
 'r15_old_syntactic_degree':original_r15,'r15_rewritten_term_degree_bounds':term_degrees,'r15_exact_degree':d(r15),
 'scale_exact_degree':d(3600218),'native_Z_exact_degree':d(3600216),
 'unit_factor_degree_bounds':[d(h) for h in M['extra']['unit_factors']],
 'native_unit_exact_degree':d(M['extra']['native_unit']),
 'residual_degree_bounds':[d(sq-1) for sq in squares],
 'maximal_residual_square_index_zero_based':6,'finalizer_exact_degree':mx,
 'complete_exact_degree':d(M['output']),'top_polynomial_sparse_terms_in_p_and_inputs':len(actual),
 'leading_formula':'2^138*p^23113311*ga*w^5*odd_half^15*(eta+zeta)^10*f^2*i^4*(tau_gap-eta-zeta)*H_V^2',
 'p_definition':'2^551890*Vfinal*(X+Z0)*sum(native.Shat[0:794976])',
 'ring':'Z[all 797141 independent coordinates], each coordinate degree one',
 'assumptions':['Frozen constant recipes denote fixed integer constants','No residual equation, witness positivity, or native constraint is used as a polynomial identity'],
 'scan_seconds':time.monotonic()-start,
 'resources':{'address_space_limit_bytes':MAX_MEMORY,'cpu_limit_seconds':MAX_SECONDS,'wall_time_limit_seconds':MAX_SECONDS,'sparse_term_limit':MAX_TERMS,'max_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'total_seconds':time.monotonic()-started},
}
(DEST/args.output).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
