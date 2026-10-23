#!/usr/bin/env python3
"""Exact standard-library audit of degree-separated source extraction.
Checks formal polynomial identities; does not prove inherited compiler semantics.
"""
import ast,collections,hashlib,itertools,json,math,sys
from pathlib import Path
R=Path(__file__).resolve().parent
SOURCE_SHA256='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'

def require(ok,reason):
 if not ok:raise ValueError(reason)
def add(a,b,k=1):
 out=dict(a)
 for m,c in b.items():out[m]=out.get(m,0)+k*c
 return {m:c for m,c in out.items() if c}
def mul(a,b):
 out=collections.defaultdict(int)
 for m,c in a.items():
  for n,d in b.items():out[tuple(x+y for x,y in zip(m,n))]+=c*d
 return {m:c for m,c in out.items() if c}
def parse(text,names,aliases):
 zero=(0,)*len(names)
 def rec(node):
  if isinstance(node,ast.Constant) and type(node.value)==int:return {zero:node.value} if node.value else {}
  if isinstance(node,ast.Name):
   if node.id in aliases:return rec(ast.parse(aliases[node.id].replace('^','**'),mode='eval').body)
   require(node.id in names,'unknown symbol');m=list(zero);m[names.index(node.id)]=1;return {tuple(m):1}
  if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return {m:-c for m,c in rec(node.operand).items()}
  if isinstance(node,ast.BinOp):
   a=rec(node.left)
   if isinstance(node.op,ast.Pow):
    require(isinstance(node.right,ast.Constant) and type(node.right.value)==int and 0<=node.right.value<=4,'unsupported exponent')
    out={zero:1}
    for _ in range(node.right.value):out=mul(out,a)
    return out
   b=rec(node.right)
   if isinstance(node.op,ast.Add):return add(a,b)
   if isinstance(node.op,ast.Sub):return add(a,b,-1)
   if isinstance(node.op,ast.Mult):return mul(a,b)
  raise ValueError('unsupported polynomial AST')
 return rec(ast.parse(text.replace('^','**'),mode='eval').body)

def audit(codepath=None,write=False):
 raw=(R/'parent_source.json').read_bytes();require(hashlib.sha256(raw).hexdigest()==SOURCE_SHA256,'parent source hash')
 src=json.loads(raw);names=src['variables']+src['constants'];n=len(src['variables'])
 require(n==31 and src['constants']==['beta','K0','MC','MF'],'parent dimensions and ports')
 require(src['domain']=='strictly positive integers','source domain')
 rows=[]
 for i,r in enumerate(src['equations']):
  require(r['number']==i+1,'row numbering')
  sparse={tuple(t['powers']):t['coefficient'] for t in r['terms']}
  require(len(sparse)==len(r['terms']),'duplicate source monomial')
  require(sparse==parse(r['residual'],names,src['affine_abbreviations']),'source residual/term identity')
  rows.append(sparse)
 require(len(rows)==22,'source row count')
 transformed=rows[:]
 transformed[13]=add(rows[13],rows[1]);transformed[14]=add(rows[14],rows[2])
 require(add(transformed[13],transformed[1],-1)==rows[13] and add(transformed[14],transformed[2],-1)==rows[14],'inverse row-operation identities')
 transformed=[{m:-c for m,c in row.items()} for row in transformed]
 blocks=[]
 for row in transformed:
  block=collections.defaultdict(dict)
  for mon,c in row.items():
   pair=tuple(i for i,e in enumerate(mon[:n]) for _ in range(e));require(len(pair)<=2,'not quadratic')
   fac=2 if len(pair)!=2 or pair[0]==pair[1] else 1
   block[pair][mon[n:]]=c*fac
  blocks.append(dict(block))
 path=Path(codepath) if codepath else R/'split_code.json';code=json.loads(path.read_text())
 require(code['source_row_operations']==[[14,2,1],[15,3,1]] and code['global_sign']==-1,'row operations changed')
 w=code['weights'];order=code['order'];q=code['targets']
 require(len(w)==n and all(type(x)==int and x>0 for x in w) and len(set(w))==n,'weights invalid')
 require(sorted(order)==list(range(1,23)),'row order')
 require(len(q)==22 and len(set(q))==22 and all(type(x)==int and x>=0 for x in q),'targets invalid')
 allmons={0:[()],1:[(i,) for i in range(n)],2:list(itertools.combinations_with_replacement(range(n),2))}
 sumgroups={d:collections.defaultdict(list) for d in range(3)}
 for d,mons in allmons.items():
  for mon in mons:sumgroups[d][sum(w[i] for i in mon)].append(mon)
 active=set(p for b in blocks for p in b)
 for p in active:require(sumgroups[len(p)][sum(w[i] for i in p)]==[p],'same-degree supported label collision')
 kernels=[{} for _ in range(3)];targets=dict(zip(q,order));extracted={r:{} for r in order};checks=matches=0
 for row,target in zip(order,q):
  for pair,coeff in blocks[row-1].items():
   d=len(pair);exponent=target-sum(w[i] for i in pair)
   require(exponent>=0,'negative kernel exponent');require(exponent not in kernels[d],'same-degree kernel overlap')
   kernels[d][exponent]=coeff
   for mon in allmons[d]:
    checks+=1;at=exponent+sum(w[i] for i in mon)
    if at in targets:
     require(targets[at]==row and mon==pair,'target contamination');matches+=1
     multiplicity=2 if d==2 and mon[0]!=mon[1] else 1
     wp=[0]*n
     for i in mon:wp[i]+=1
     for pp,c in coeff.items():
      full=tuple(wp)+pp;extracted[row][full]=extracted[row].get(full,0)+multiplicity*c
 for row in order:require(extracted[row]=={m:2*c for m,c in transformed[row-1].items()},'formal target polynomial mismatch')
 M=max(w);degrees=[max(k) if k else -1 for k in kernels];height=max(a+d*M for d,a in enumerate(degrees))
 require(code['max_weight']==M and code['kernel_degrees']==degrees and code['convolution_height']==height and code['maximum_target']==max(q),'stale size data')
 require(min(e for k in kernels for e in k)==0,'avoidable common source shift')
 require((M,max(q),degrees,height)==(108,1939,[1939,1842,1738],1954),'not the certified positivity layout')
 require(kernels[2][1738]=={(1,0,0,0):1},'quadratic kernel leading coefficient')
 require(kernels[1][1842]=={(0,0,0,0):2} and kernels[0][1939]=={(0,0,0,0):2},'linear and constant leading coefficients')
 # Conservative exact native-tuple coefficient bound, independent of port values.
 bitlengths=[1064921,1070004,1064921,1064922]
 majorants=[sum(abs(c)*(1<<sum(e*b for e,b in zip(pp,bitlengths))) for pp,c in co.items()) for k in kernels for co in k.values()]
 Cexp=max(majorants).bit_length();require(Cexp<=2134927,'coefficient majorant exceeds inherited floor')
 require(2134940>=Cexp+12,'fixed base floor too small')
 output={'status':'PASS','source_sha256':SOURCE_SHA256,'source_variables':n,'source_rows':22,'row_operations':code['source_row_operations'],'formal_inverse_row_identities':2,'independently_parsed_residuals':22,'supported_monomials_by_degree':[sum(len(p)==d for p in active) for d in range(3)],'source_records_by_degree':[sum(len(p)==d for b in blocks for p in b) for d in range(3)],'kernel_records':sum(len(k) for k in kernels),'candidate_expansion_monomials_by_degree':[len(allmons[d]) for d in range(3)],'finite_source_expansion_interactions':checks,'target_contributions':matches,'formal_target_identities':22,'max_weight':M,'maximum_target':max(q),'kernel_degrees':degrees,'convolution_height':height,'N0_exponent':M+1,'N1_exponent':height+1,'N_exponent':height+M+2,'quadratic_kernel_leading_coefficient':'beta','linear_kernel_leading_coefficient':2,'constant_kernel_leading_coefficient':2,'global_sign':-1,'coefficient_bound_power_of_two':Cexp,'source_base_floor_power_of_two':2134940,'code_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'scope':'Exact universal polynomial identities and finite bounds. Inherited unbounded compiler and arithmetic-finalizer semantics are not proved by this checker.'}
 data={'variables':src['variables'],'ports':src['constants'],'source_sha256':SOURCE_SHA256,'code_sha256':output['code_sha256'],'formula':'G(B,U)=D2(B)*U^2+D1(B)*U+D0(B)','kernels':[]}
 for degree,k in enumerate(kernels):data['kernels'].append({'degree':degree,'terms':[{'exponent':e,'coefficient':[{'powers':list(pp),'coefficient':c} for pp,c in sorted(co.items())]} for e,co in sorted(k.items())]})
 if write:
  (R/'split_kernels.json').write_text(json.dumps(data,indent=2)+'\n')
 elif (R/'split_kernels.json').exists():
  require(json.loads((R/'split_kernels.json').read_text())==data,'derived kernel artifact mismatch')
 return output
if __name__=='__main__':
 code=next((a for a in sys.argv[1:] if a!='--write'),None)
 print(json.dumps(audit(code,'--write' in sys.argv),indent=2))
