"""Bounded exact common-discriminant composition scout including the strong norm."""
import argparse, hashlib, itertools, json, random
from collections import Counter
from pathlib import Path
import sympy as sp
PINS={
 'complete75_asymmetric_scale_tradeoffs.py':'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660',
 'complete75_asymmetric_scale_tradeoffs.json':'47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98',
 'complete75_normalized_strong87.py':'7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8',
 'complete75_coupled_index_linear88.py':'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
PAIRS={'main':('R14','R10a'),'input':('exponent_rhs','index_rhs'),'strong':('f','ic2')}
def need(ok,msg):
 if not ok: raise ValueError(msg)
def exact(a,b):
 if type(a) is not type(b): return False
 if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (list,tuple): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def source(root):
 for n,h in PINS.items():need(sha(root/n)==h,'Pin mismatch '+n)
 r=json.loads((root/'complete75_asymmetric_scale_tradeoffs.json').read_text())['source'][0]
 need(r['normalized'] is True,'wrong canonical source')
 return [tuple(x) for x in r['source']]
def compile_rows(d,out='polynomial'):
 # Exact literal commutative CSE only. No algebraic factoring, division or free constants.
 rows=[]; seen={}; done={}; active=set(); n=0
 def visit(v):
  nonlocal n
  if type(v) is int or v not in d:return v
  if v in done:return done[v]
  need(v not in active,'cycle');active.add(v)
  op,a,b=d[v];a,b=visit(a),visit(b)
  if type(a) is int and type(b) is int:
   z=a+b if op=='+' else a-b if op=='-' else a*b
  elif op=='+' and a==0:z=b
  elif op in ('+','-') and b==0:z=a
  elif op=='*' and (a==0 or b==0):z=0
  elif op=='*' and a==1:z=b
  elif op=='*' and b==1:z=a
  else:
   if op in ('+','*') and repr(a)>repr(b):a,b=b,a
   key=(op,a,b)
   if key in seen:z=seen[key]
   else:
    z='gate_'+str(n);n+=1;rows.append((z,op,a,b));seen[key]=z
  active.remove(v);done[v]=z;return z
 output=visit(out)
 return rows,output,done

def closure(rows,output):
 names={r[0] for r in rows};need(len(names)==len(rows),'duplicate name')
 free={v for _,_,a,b in rows for v in (a,b) if type(v) is str and v not in names};avail=set(free)
 for n,op,a,b in rows:
  need(type(n) is str and op in ('+','-','*') and n not in avail,'gate contract')
  need(all(type(v) is int or type(v) is str and v in avail for v in (a,b)),'topological closure');avail.add(n)
 live=set();nodes={n:(a,b) for n,_,a,b in rows}
 def walk(v):
  if v not in nodes or v in live:return
  live.add(v)
  for w in nodes[v]:walk(w)
 walk(output);need(live==names,'dead gate')
 return sorted(free)
def run(rows,output,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=a if type(a) is int else e[a];b=b if type(b) is int else e[b]
  e[n]=a+b if o=='+' else a-b if o=='-' else a*b
 return e[output] if type(output) is str else output

def make(old,order,signs,algorithms,special=False):
 d={n:(o,a,b) for n,o,a,b in old};counter=0
 def g(op,a,b):
  nonlocal counter
  n='new_'+str(counter);counter+=1;d[n]=(op,a,b);return n
 def add(a,b,s=1):return g('+' if s==1 else '-',a,b)
 def mul(a,b):return g('*',a,b)
 def compose(x,y,u,v,s,algorithm):
  p=mul(x,u);r=mul(y,v);real=add(p,mul('A',r),s)
  if algorithm=='schoolbook':imag=add(mul(y,u),mul(x,v),s)
  else:
   # (x+y)(u+s*v)-xu-s*yv = yu+s*xv.
   mixed=mul(add(x,y),add(u,v,s));imag=add(add(mixed,p,-1),r,-s)
  return real,imag
 if special:
  # t=i*c²; factor c from D*t +/- f*c, retaining the literal Ac2 shared form.
  need(order==('main','strong'),'special pair')
  s=signs[0];r=mul('i','R10a');u=add(mul('R14','f'),mul('Ac2',r),s)
  v=add('f',mul('R14',r),s)
  joint=add(mul(u,u),mul('Ac2',mul(v,v)),-1)
 else:
  x,y=PAIRS[order[0]]
  for item,s,algorithm in zip(order[1:],signs,algorithms):x,y=compose(x,y,*PAIRS[item],s,algorithm)
  joint=add(mul(x,x),mul('A',mul(y,y)),-1)
 selected={'norm_'+name for name in order};remaining=[];inserted=False
 for f in FACTORS:
  if f in selected:
   if not inserted:remaining.append(joint);inserted=True
  else:remaining.append(f)
 product=remaining[0]
 for f in remaining[1:]:product=mul(product,f)
 d['polynomial']=('-',product,1)
 rows,out,mapping=compile_rows(d)
 return d,joint,rows,out,mapping

def prove_joint(d,joint,order):
 A,D,c,mu,k,f,i=sp.symbols('Delta D c mu kappa f i')
 cuts={'A':A,'R14':D,'R10a':c,'exponent_rhs':mu,'index_rhs':k,'f':f,'i':i}
 memo=dict(cuts)
 def expr(n):
  if type(n) is int:return sp.Integer(n)
  if n in memo:return memo[n]
  o,a,b=d[n];a,b=expr(a),expr(b);memo[n]=a+b if o=='+' else a-b if o=='-' else a*b;return memo[n]
 norms={'main':D**2-A*c**2,'input':mu**2-A*k**2,'strong':f**2-A*i**2*c**4}
 expected=sp.prod(norms[n] for n in order)
 need(sp.expand(expr(joint)-expected)==0,'literal composition identity')
 # No retained definition changed. The complete output is explicitly the
 # unchanged other factors times this joint factor, minus 1.
 return 1

def verify(root):
 old=source(root);base={n:(o,a,b) for n,o,a,b in old};r0,o0,_=compile_rows(base)
 free=closure(r0,o0);need(len(r0)==87,'CSE baseline changed')
 cases=[]
 for order in (('main','strong'),('input','strong')):
  for s,a in itertools.product((-1,1),('schoolbook','karatsuba')):cases.append((order,(s,),(a,),False))
 for order in itertools.permutations(PAIRS):
  for ss in itertools.product((-1,1),repeat=2):
   for aa in itertools.product(('schoolbook','karatsuba'),repeat=2):cases.append((order,ss,aa,False))
 for s in (-1,1):cases.append((('main','strong'),(s,),('factor_c',),True))
 rng=random.Random(871692026);records=[];best={};symbolic=0;numeric=signed=0
 for order,ss,aa,special in cases:
  d,joint,rows,out,mapping=make(old,order,ss,aa,special)
  need(closure(rows,out)==free,'free input changed')
  need(all(d[n]==v for n,v in base.items() if n!='polynomial'),'old definition changed')
  symbolic+=prove_joint(d,joint,order)
  counts=Counter(o for _,o,_,_ in rows)
  for cse in range(24):
   v={n:rng.randrange(-3,4) if cse%2 else rng.randrange(1,4) for n in free}
   B=(16,32,64)[cse%3]
   v.update(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)
   need(run(rows,out,v)==run(r0,o0,v),'complete polynomial identity');numeric+=1;signed+=cse%2
  family='main_strong_factored' if special else 'pair_'+order[0] if len(order)==2 else 'all_three'
  item={'order':order,'signs':ss,'algorithms':aa,'factored_c':special,'operations':len(rows),'M':counts['*'],'A':counts['+']+counts['-']}
  records.append(item)
  if family not in best or len(rows)<best[family]['operations']:
   best[family]={**item,'complete_source':rows,'output':out,'free_inputs':free,'all_gates_live':True}
 # The new local finalization variants are intentionally negative results.
 need(all(r['operations']>=87 for r in records),'Unexpected saving: review before publishing')
 return {'status':'PASS_BOUNDED_NEGATIVE_RESULT','pins':PINS,'baseline':{'operations':87,'M':48,'A':39,'degree':169,'positive_witnesses':19},'cases':records,'best_by_family':best,'checks':{'circuit_choices':len(cases),'exact_literal_joint_polynomial_identities':symbolic,'complete_finalizer_factorizations':len(cases),'complete_numeric_polynomial_cases':numeric,'signed_numeric_cases':signed,'unchanged_old_definition_checks':len(cases)*86},'scope':'New compositions involving the normalized strong norm: two pairs, all 96 ordered/sign/algorithm triple choices, and two c-factored main/strong schedules. Exact entire polynomial on all integer tuples; no witness/domain/sign/rank change. No general circuit lower bound.'}
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run without -O')
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
 result=json.loads(json.dumps(verify(a.root.resolve())))
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'receipt mismatch')
 if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(result['status']);print({k:(v['operations'],v['M'],v['A']) for k,v in result['best_by_family'].items()});print(result['checks'])
