"""Independent new checker: reads restored Library JSON as inert data, executes no upstream code."""
import ast,gzip,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
L=R.parent/'review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23'
P=1000000007

def req(x,m):
 if not x:raise ValueError(m)
def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def add(a,b,sign=1):
 c=[0]*max(len(a),len(b))
 for i,x in enumerate(a):c[i]=x
 for i,x in enumerate(b):c[i]=(c[i]+sign*x)%P
 return trim(c)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%P
 return trim(c)
def ev(s,e):
 def go(n):
  if isinstance(n,ast.Name):return e[n.id]
  if isinstance(n,ast.Constant):req(isinstance(n.value,int),'literal');return [n.value%P]
  if isinstance(n,ast.UnaryOp):return [(-x)%P for x in go(n.operand)]
  req(isinstance(n,ast.BinOp),'ast')
  a=go(n.left)
  if isinstance(n.op,ast.Pow):
   k=ast.literal_eval(n.right);req(isinstance(k,int) and 0<=k<=100,'exponent');r=[1]
   for _ in range(k):r=mul(r,a)
   return r
  b=go(n.right)
  if isinstance(n.op,ast.Add):return add(a,b)
  if isinstance(n.op,ast.Sub):return add(a,b,-1)
  if isinstance(n.op,ast.Mult):return mul(a,b)
  raise ValueError('operator')
 return go(ast.parse(s,mode='eval').body)
# Actual frozen coefficient bytes independently authenticated before specialization.
b=json.loads((R.parent/'low_degree/BINDING.json').read_text());fixed={}
for n,d in b['ports'].items():
 raw=gzip.decompress((R.parent/'low_degree'/d['path']).read_bytes());req(hashlib.sha256(raw).hexdigest()==d['raw_sha256'],'fixed hash');fixed[n]=int.from_bytes(raw,'little')%P
results=[]
for name in ['degree20_20_rank_register','degree28_19','degree32_18','degree88_17']:
 path=L/'transport'/(name+'.json');d=json.loads(path.read_text());cert=d['degree_certificate'];req(cert['prime']==P,'prime');req(cert['actual_fixed_ports_mod_prime']==fixed,'actual ports');req(len(d['variables'])==d['variable_count'],'count');req(len(d['factored_residuals'])==d['residual_count'],'rows');e={n:[0,cert['slopes'][n]] for n in d['variables']};e.update({n:[v] for n,v in fixed.items()})
 for n,x in d['polynomial_abbreviations']:e[n]=ev(x,e)
 polys=[ev(x,e) for x in d['factored_residuals']];degrees=[len(x)-1 for x in polys];i=cert['residual_index_zero_based'];degree=cert['residual_exact_degree'];req(degrees[i]==degree,'degree');req(polys[i][-1]==cert['coefficient_of_t_to_residual_degree'],'leading coefficient');req(max(degrees)*2==d['exact_degree'],'max');req(all(x<=y for x,y in zip(degrees,cert['residual_degree_upper_bounds'])),'bounds')
 results.append({'packet':name,'unknowns':d['variable_count'],'residuals':d['residual_count'],'degree':d['exact_degree'],'literal_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'specialized_residual_degrees':degrees,'leading_coefficient_mod_prime':polys[i][-1]})
print(json.dumps({'status':'pass','scope':'exact univariate modular coefficient replay, not an independent full metatheorem proof','library_archive_sha256':'7c21ff5d05ef52c754399a6e62f37ac7622baa6e82a702d855bfb68d82fc1a4a','library_file_id':'libfile_299513832b988191a5114e109ffe62dd','results':results},indent=2))
