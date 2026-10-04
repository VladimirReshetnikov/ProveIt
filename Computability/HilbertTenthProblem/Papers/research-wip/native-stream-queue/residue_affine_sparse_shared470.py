"""Fresh two-program U21 476-to-470 rewrite; frozen predecessors are inert data."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random
ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'residue_affine_sparse_shared476.py':'52e09d2b3474e37c6116e16b7a1ee59395a337a5ff381b4881ae616ecbaafddf',
 'residue_affine_sparse_shared476.json':'90e6e265ae1eb9a1cd1239255c14da3d3c6e5841f330f7a6220536d182778ba8',
 'residue_affine_sparse_shared476.md':'cbd4d632b813f0ad34a9e5b35894d187ca229c14f1d4cf3af269a518ab57fcd4',
 'residue_affine_sparse_program_radix504.md':'4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549',
 'residue_affine_sparse_factored.md':'b169236c449623049759b7ac0877b2202b3aba389ace8e06d31370396abb9ea7',
 'residue_affine_sparse_control_codes.md':'be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da',
 'native_binary_norm_units.py':'1f088e43e60f068f2ca7c78a607f4cc5cd4ec34b7d2d5259c9ce545f74fdfee9',
}
EDITS=[
 ['prime_selector_99','+','edge_16','control_codes__target_class_35'],
 ['prime_selector_101','+','prime_selector_99','control_codes__duplicate_state_3'],
 ['prime_selector_105','+','prime_selector_103','control_codes__duplicate_state_2'],
 ['prime_selector_107','+','prime_selector_105','control_codes__duplicate_state_5'],
 ['prime_selector_109','+','prime_selector_107','control_codes__duplicate_state_8'],
 ['control_codes__current_positive_19','+','u21_grouped_J_0','prime_selector_95'],
]
DELETED=['control_codes__current_multiple_9','prime_selector_100','prime_selector_104',
         'prime_selector_106','prime_selector_108','prime_selector_98']
OUTPUT='norm_output'
def ck(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(v):
  d={}
  for k,x in v:ck(k not in d,'duplicate JSON key');d[k]=x
  return d
 def bad(x):raise ValueError('noninteger JSON '+x)
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def table(rows):
 d={}
 for r in rows:
  ck(type(r)is list and len(r)==4,'row shape');n,o,a,b=r
  ck(type(n)is str and n not in d and o in ('+','-','*'),'unique binary producer')
  ck(all(type(v)in (int,str)for v in(a,b)),'operand type');d[n]=r
 return d

def closure(d,roots):
 done=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is str and n not in done:
   done.add(n)
   if n in d:todo.extend(d[n][2:])
 return done

def audit(rows,ports):
 d=table(rows);seen=set(ports);count=Counter()
 for n,o,a,b in rows:
  ck(n not in seen and all(type(v)is int or v in seen for v in(a,b)),'SSA/topology')
  seen.add(n);count[o]+=1
 ck(closure(d,[OUTPUT])==seen,'all source rows and supplied ports live')
 return dict(operations=len(rows),multiplications=count['*'],additions_subtractions=count['+']+count['-'])

def rewrite(old):
 before=encode(old);d={n:list(r)for n,r in table(old).items()}
 for r in EDITS:ck(r[0]in d,'edit target exists');d[r[0]]=list(r)
 live=closure(d,[OUTPUT]);ck(sorted(set(d)-live)==DELETED,'exact six private deletions')
 result=[];seen=set();active=set()
 def emit(n):
  if type(n)is int or n not in d or n in seen:return
  ck(n not in active,'simultaneous rewrite cycle');active.add(n)
  for v in d[n][2:]:emit(v)
  active.remove(n);seen.add(n);result.append(d[n])
 for r in old:
  if r[0]in live:emit(r[0])
 ck(encode(old)==before,'parent array mutated')
 ck(seen==set(d)&live,'whole live DAG emitted')
 return result

def affine(rows,root,raw=False):
 d=table(rows);z=(0,)*37
 env={f'edge{i}_hat':tuple(1 if j==i or (raw and j==36) else 0 for j in range(37))for i in range(36)}
 # Default coordinates are the actual supplied hats; raw=True uses hat_i=E_i+1.
 def get(v):
  if type(v)is int:return z[:36]+(v,)
  if v in env:return env[v]
  ck(v in d,'unknown affine leaf '+v)
  _,op,a,b=d[v];a,b=get(a),get(b)
  if op in ('+','-'):q=tuple(x+(y if op=='+'else-y)for x,y in zip(a,b))
  elif not any(a[:36]):q=tuple(a[36]*y for y in b)
  elif not any(b[:36]):q=tuple(b[36]*x for x in a)
  else:raise ValueError('non-affine cone '+v)
  env[v]=q;return q
 return get(root)

def contract(old,new,ports):
 a,b=table(old),table(new);targets={r[0]for r in EDITS};proof=[]
 ck(set(a)-set(b)==set(DELETED)and not set(b)-set(a),'only deleted register names')
 for n in b:
  expected=next(r for r in EDITS if r[0]==n) if n in targets else a[n]
  ck(b[n]==expected,'literal retained definition '+n)
 for n in sorted(targets):
  x,y=affine(old,n),affine(new,n);ck(x==y,'exact whole affine cut '+n)
  rawx,rawy=affine(old,n,True),affine(new,n,True)
  ck(rawx==rawy,'raw selector identity '+n)
  ck(x[:36]==rawx[:36] and x[36]==rawx[36]-sum(rawx[:36]),'hat/raw substitution '+n)
  proof.append(dict(register=n,old_definition=a[n],new_definition=b[n],hat_coefficients=list(x),raw_selector_coefficients=list(rawx)))
 pool={}
 def token(x):
  if x not in pool:pool[x]=len(pool)
  return pool[x]
 base={n:token(('port',n))for n in ports};values=[]
 for rows in(old,new):
  e=base.copy()
  for n,o,x,y in rows:
   if n in targets:
    # Bind each exact affine identity to the actual hat expressions E_i=hat_i-1.
    coeff=tuple(affine(rows,n));e[n]=token(('affine',tuple(e[f'edge{i}_hat']for i in range(36)),coeff))
   else:
    xv,yv=(token(('integer',v))if type(v)is int else e[v]for v in(x,y));e[n]=token((o,xv,yv))
  values.append(e)
 ck(all(values[0][n]==v for n,v in values[1].items()),'every retained register/full output identity')
 # Every omitted producer was internal to its replaced linear cone.
 users={n:[r[0]for r in old if n in r[2:]]for n in DELETED}
 ck(all(len(v)==1 and v[0]in targets for v in users.values()),'deleted rows private')
 return dict(local_affine_identities=proof,private_deleted_consumers=users,
  all_value_retained_registers=len(new),all_ring_identity='F470=F476 on identical supplied coordinates over every commutative ring',
  actual_selector_hats_bound=True)

def degree_bound(rows,ports):
 by=table(rows);p='native__';expected={
 'R15':['-','native__L15','native__Ac2'],'L15':['*','native__R14','native__R14'],
 'R14':['+','native__D1','native__gam'],'D1':['+','native__wn2','native__cam2'],
 'cam2':['*','native__R10a','native__R12'],'A':['+','native__a_square','native__a4m5'],
 'a_square':['*','native__R12','native__R12'],'Ac2':['*','native__A','native__c2'],
 'c2':['*','native__R10a','native__R10a'],'a4m5':['+','native__a4',3],
 'a4':['*',4,'native__R12'],'gam':['*','native__ga','native__a4m5']}
 for n,r in expected.items():ck(by[p+n]==[p+n]+r,'literal main norm cancellation '+n)
 # Independently expand the small norm identity at X,a,c,G,H.
 names=['X','a','c','G','H'];zero=(0,)*5
 def num(k):return {zero:k}if k else{}
 def v(n):return {tuple(int(i==names.index(n))for i in range(5)):1}
 def add(a,b,s=1):
  d=a.copy()
  for m,c in b.items():d[m]=d.get(m,0)+s*c
  return {m:c for m,c in d.items()if c}
 def mul(a,b):
  d={}
  for m,c in a.items():
   for n,e in b.items():
    k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
  return {k:c for k,c in d.items()if c}
 X,a,c,G,H=map(v,names);D=add(add(X,mul(a,c)),G)
 exact=add(mul(D,D),mul(add(mul(a,a),H),mul(c,c)),-1)
 ck(len(exact)==6,'six term main norm')
 degrees={n:1 for n in ports};raw=degrees.copy();bounds=[]
 for n,o,x,y in rows:
  d1,d2=(0 if type(t)is int else degrees[t]for t in(x,y));degrees[n]=d1+d2 if o=='*'else max(d1,d2)
  r1,r2=(0 if type(t)is int else raw[t]for t in(x,y));raw[n]=r1+r2 if o=='*'else max(r1,r2)
  if n==p+'R15':
   cuts=[degrees[p+k]for k in ['wn2','R12','R10a','gam','a4m5']]
   bounds=[sum(i*j for i,j in zip(m,cuts))for m in exact];degrees[n]=max(bounds)
 factors=['R15','P17','first_unit','bs_q','f_square_minus_one','index_unit','linear_unit']
 fv=[degrees[p+n]for n in factors]+[degrees['sparse_repunit_unit']]
 ck(fv==[827,1926,448,66,1032,380,380,3],'guarded factor bounds')
 ck(degrees[OUTPUT]==5160 and raw[OUTPUT]==5227,'whole exact-identity degree upper')
 return dict(polynomial_degree_upper_bound=degrees[OUTPUT],naive_gate_degree_upper=raw[OUTPUT],
  main_norm_identity_variables=names,main_norm_coefficients=[[list(m),c]for m,c in sorted(exact.items())],
  main_norm_cut_bounds=cuts,main_norm_bound=degrees[p+'R15'],main_norm_naive_bound=raw[p+'R15'],
  main_norm_term_bounds=sorted(bounds),factor_degree_bounds=fv,
  factor_sum=sum(fv),maximum_residual_degree=max(degrees[f'norm_residual{i}']for i in range(6)),
  exact_degree_claimed=False,degree_convention='Every supplied port has degree1; fixed integer literals degree0, hence also an upper bound after fixing program')

def evaluate(rows,values,mod=None):
 e=values.copy()
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  v=a*b if o=='*'else a+b if o=='+'else a-b;e[n]=v%mod if mod else v
 return e

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'dependency '+n)
 parent=read(root/'residue_affine_sparse_shared476.json');ck(parent['source_sha256']==PINS['residue_affine_sparse_shared476.py'],'parent helper binding')
 p=parent['packet'];original=encode(p);old=p['source'];ports=p['parameters']+p['witnesses']
 ck(p['parameters']==['program','radix_program','input']and p['fixed_program_parameters']==['program','radix_program'],'two-program interface')
 ck(p['source_sha256']==sha(encode(old)),'parent array binding')
 prior=audit(old,ports);ck(prior==dict(operations=476,multiplications=176,additions_subtractions=300),'parent count')
 new=rewrite(old);led=audit(new,ports);ck(led==dict(operations=470,multiplications=175,additions_subtractions=295),'complete emitted count')
 ck(len(ports)==70 and len(p['witnesses'])==67,'same supplied coordinates')
 identity=contract(old,new,ports);degree=degree_bound(new,ports)
 by=table(new);native=[r for r in old if r[0].startswith('native__')]
 ck(len(native)==72 and all(by[r[0]]==r for r in native),'literal native rows')
 final=old[-20:];ck(final[-1][0]==OUTPUT and all(by[r[0]]==r for r in final),'literal complete finalizer')
 ck(all(by[f'norm_residual{i}']==table(old)[f'norm_residual{i}'] for i in range(6)),'literal six ordinary residuals')
 certificate=[r for r in new if r[0]not in {r[0]for r in final}];cc=Counter(r[1]for r in certificate)
 cle=dict(operations=len(certificate),multiplications=cc['*'],additions_subtractions=cc['+']+cc['-'],equations=7,witnesses=67)
 ck(cle==dict(operations=450,multiplications=168,additions_subtractions=282,equations=7,witnesses=67),'certificate count')
 height_radix=[['height_85','+','input','height_slack'],['radix_86','*','radix_program','height_85']]
 ck(all(table(old)[r[0]]==by[r[0]]==r for r in height_radix),'literal two-program height/radix')
 ck(p['valid_recipe']=='C is a positive dyadic integer, C>=64 and C>program; default control plan only.','parent fixed recipe')
 rng=random.Random(47020261004)
 for prime in [1000000007,1000000009]:
  for case in range(16):
   v={n:rng.randrange(-19,20)for n in ports};a,b=evaluate(old,v,prime),evaluate(new,v,prime)
   ck(all(a[n]==b[n]for n in by),'all retained modular values')
 for case in range(4):
  v={n:Fraction(rng.randrange(-1,2),2)for n in ports};a,b=evaluate(old,v),evaluate(new,v)
  ck(all(a[n]==b[n]for n in by),'all retained rational values')
 ck(encode(p)==original,'whole parent packet immutable')
 new_packet=dict(p,source=new,ledger=dict(led,witnesses=67),certificate_ledger=cle,source_sha256=sha(encode(new)),literal_height_radix_rows=height_radix)
 ck(new_packet['polynomial_degree_upper_bound']==degree['polynomial_degree_upper_bound'] and new_packet['exact_degree_claimed'] is False,'inherited degree bound verified afresh')
 return dict(status='PASS_U21_SHARED470',source_sha256=sha(Path(__file__).read_bytes()),dependencies=PINS,
  packet=new_packet,exact_contract=identity,degree_proof=degree,
  boundaries=dict(native_rows_literal=72,finalizer_rows_literal=20,ordinary_residuals_literal=6,height_radix_literal=True),
  finite_checks=dict(whole_signed_modular_pairs=32,whole_signed_rational_pairs=4,all_retained_values_per_pair=len(new),native_history_claim=False),
  scope='Identical full polynomial and all supplied positive zero tuples to the two-program476 parent; fixed E=3^e and dyadic C>=64,C>E, ordinary x>0, B=C*(x+height_slack),67w; no map to471, circuit minimum, exact degree, new trajectory or improvement to84 claimed')
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=build(a.root)
 if a.output:
  with a.output.open('x')as f:f.write(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(encode(r)==encode(read(a.expect)),'type-exact receipt')
 print(r['status'],r['packet']['ledger'],'degree <=',r['degree_proof']['polynomial_degree_upper_bound'])
if __name__=='__main__':main()
