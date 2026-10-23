if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Independent inert-sparse-quadratic reader and Jones coefficient recipe.
The only executable inputs are this newly authored audit and Python stdlib.
"""
import ast,json,itertools,math,hashlib,sys
from pathlib import Path
from collections import defaultdict
HERE=Path(__file__).resolve().parent

def plus(a,b):
 out=defaultdict(int,a)
 for mon,c in b.items():out[mon]+=c
 return {m:c for m,c in out.items() if c}
def times(a,b):
 out=defaultdict(int)
 for m,c in a.items():
  for n,d in b.items():out[tuple(x+y for x,y in zip(m,n))]+=c*d
 return {m:c for m,c in out.items() if c}
def parse_expression(expression,names):
 zero=(0,)*len(names)
 def read(n):
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return {zero:n.value} if n.value else {}
  if isinstance(n,ast.Name):return {tuple(int(x==n.id) for x in names):1}
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {m:-c for m,c in read(n.operand).items()}
  if isinstance(n,ast.BinOp):
   a=read(n.left)
   if isinstance(n.op,ast.Pow):
    assert isinstance(n.right,ast.Constant) and 0<=n.right.value<=8
    r={zero:1}
    for _ in range(n.right.value):r=times(r,a)
    return r
   b=read(n.right)
   if isinstance(n.op,ast.Add):return plus(a,b)
   if isinstance(n.op,ast.Sub):return plus(a,{m:-c for m,c in b.items()})
   if isinstance(n.op,ast.Mult):return times(a,b)
  raise ValueError(ast.dump(n))
 return read(ast.parse(expression.replace('^','**'),mode='eval').body)
def shift(poly,n):
 out=defaultdict(int)
 for m,c in poly.items():
  slots=[i for i in range(n) if m[i]]
  for choices in itertools.product(*(range(m[i]+1) for i in slots)):
   mon=list(m);coeff=c
   for i,v in zip(slots,choices):mon[i]=v;coeff*=math.comb(m[i],v)
   out[tuple(mon)]+=coeff
 return {m:c for m,c in out.items() if c}
def records(poly):return [dict(powers=list(m),coefficient=c) for m,c in sorted(poly.items())]
def prepare(parent):
 nu=len(parent['variables']);ports=parent['constants'];total={};norm=[]
 for eq in parent['equations']:
  raw={tuple(t['powers']):t['coefficient'] for t in eq['terms']}
  assert all(len(m)==nu+4 and sum(m[:nu])<=2 for m in raw)
  changed=shift(raw,nu);norm.append({m[nu:]:c for m,c in changed.items() if not any(m[:nu])})
  total=plus(total,times(changed,changed))
 grouped=defaultdict(dict)
 for m,c in total.items():grouped[(0,)+m[:nu]][m[nu:]]=c
 coeff=[]
 for k,(alpha,poly) in enumerate(sorted(grouped.items())):
  fac=math.factorial(4-sum(alpha))*math.prod(math.factorial(x) for x in alpha)
  coeff.append(dict(name=f'c{k:04d}',alpha=list(alpha),expo=sum(x*5**i for i,x in enumerate(alpha)),coefficient_polynomial_in_fixed_ports=records({m:c*fac for m,c in poly.items()})))
 assert norm[4]=={(0,0,0,0):1},norm[4]
 ti=parent['variables'].index('tau');mon=[0]*(nu+4);mon[ti]=4;assert total[tuple(mon)]==1
 constants=dict(nu=nu,L=5**(nu+1),fixed_port_order=ports,coefficient_records=coeff,dummy_input=1,bounded_sum_cardinality=math.comb(nu+5,4),coefficient_multiplier='(4-sum(alpha))! * product(alpha_j!)',normalization='P(x,n)=sum r_j(n+1)^2; the fifth residual equals 1 at all original variables=1, so P(x,0)>0.',y_index='sum((z_index+c_alpha)*(2*z_index)^(L-expo(alpha)) over alpha in N^(nu+1),sum(alpha)<=4; unlisted c_alpha=0)',u_index_unused_by_body='sum((2*z_index)^(5^j), j=1..nu)',parent_sha256=None)
 return constants,dict(coordinate_order=['n_'+s for s in parent['variables']]+ports,terms=records(total),degree_in_unknowns=4)
def main():
 src=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(exist_ok=True,parents=True)
 p=json.loads(src.read_text());c,q=prepare(p);c['parent_sha256']=hashlib.sha256(src.read_bytes()).hexdigest();c['parent_file']=src.name
 (out/'coefficients.json').write_text(json.dumps(c,indent=2)+'\n');(out/'shifted_quartic.json').write_text(json.dumps(q,separators=(',',':'))+'\n')
 print(json.dumps(dict(nu=c['nu'],coefficient_records=len(c['coefficient_records']),shifted_terms=len(q['terms']),parent_sha256=c['parent_sha256']),indent=2))
if __name__=='__main__':main()
