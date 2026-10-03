"""Independent finite five-unit census and complete109/28 leading-form audit.

Reads authenticated emitted arithmetic. Imports no historical author module.
"""
import argparse,hashlib,itertools,json,math
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete109_index_unit_tradeoffs107.py':'d255896294684f8d6411d992f5f0ba60a7f4051aa841d7e325f5347d64c23600','complete109_index_unit_tradeoffs107.json':'3d8d8d473cc866ebd585ac5605648839cfe014e98b5be2a10938cc0dfcfe12b3','complete109_index_unit_tradeoffs107.md':'928f760d73a7da081eace63cfcb144f41cd4271fcd92fbc3860d482738b16b9b','review_asymmetric_retained109_math.md':'0f9ff2fc994d54af9221e604cd9ec32890539e53a5fae3d951ad064fd64c04c5','review_complete109_index_unit_tradeoffs107.md':'ad9152d78f58442b7699d873f1bdc2c130bad8325810ae9e512ea2467a1206ab','../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d','../../1980/PELL_RELAXED_AUXILIARY_PROOF.md':'9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90','../../1980/HALF_PARAMETER_PELL_92_PROOF.md':'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b','pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992'}
LABELS=('N0','Nm','Ni','Na','Nk');PORTS=('first_unit','main_unit','input_unit','aux_unit','index_unit');DEGREES=(12,4,7,10,7)
class P(dict):
 def __init__(self,x=0):
  if type(x)is str:super().__init__({(x,):1})
  elif type(x)is int:super().__init__({():x}if x else{})
  else:super().__init__(x)
 def __add__(self,x):
  r=dict(self)
  for m,c in P(x).items():r[m]=r.get(m,0)+c
  return P({m:c for m,c in r.items()if c})
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.items()})
 def __sub__(self,x):return self+-P(x)
 def __rsub__(self,x):return P(x)+-self
 def __mul__(self,x):
  r={};other=P(x)
  for a,c in self.items():
   for b,d in other.items():m=tuple(sorted(a+b));r[m]=r.get(m,0)+c*d
  return P({m:c for m,c in r.items()if c})
 __rmul__=__mul__
 def __pow__(self,n):
  out=P(1)
  for _ in range(n):out=out*self
  return out

def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def execute(rows,env):
 env=dict(env)
 for n,op,a,b in rows:
  x=P(a)if type(a)is int else env[a];y=P(b)if type(b)is int else env[b]
  env[n]=x+y if op=='+'else x-y if op=='-'else x*y
 return env

def partitions(n):
 def extend(i,blocks):
  if i==n:yield tuple(tuple(b)for b in blocks);return
  for j in range(len(blocks)):
   bs=[list(b)for b in blocks];bs[j].append(i);yield from extend(i+1,bs)
  yield from extend(i+1,blocks+[[i]])
 yield from extend(0,[])

def emit(core,kept,partition):
 rows=[list(r)for r in core];pairs=[list(p)for p in kept]
 for gi,block in enumerate(partition):
  port=PORTS[block[0]]
  for j,i in enumerate(block[1:]):
   name=f'math_group_{gi}_{j}';rows.append([name,'*',port,PORTS[i]]);port=name
  pairs.append([port,1])
 cert=len(rows)
 for i,(a,b)in enumerate(pairs):rows += [[f'math_res_{i}','-',a,b],[f'math_sq_{i}','*',f'math_res_{i}',f'math_res_{i}']]
 out='math_sq_0'
 for i in range(1,len(pairs)):
  name=f'math_sum_{i}';rows.append([name,'+',out,f'math_sq_{i}']);out=name
 return rows,pairs,out,cert

def inspect(rows,free,output):
 known=set(free);M=0
 for n,op,a,b in rows:
  assert n not in known and op in('+','-','*')and all(type(v)is int or type(v)is str and v in known for v in(a,b))
  known.add(n);M+=op=='*'
 live={output}
 for n,op,a,b in reversed(rows):
  assert n in live;live.update(v for v in(a,b)if type(v)is str)
 assert set(free)<=live
 return dict(operations=len(rows),M=M,A=len(rows)-M)

def verify(root):
 root=Path(root)
 for name,pin in PINS.items():
  if hashlib.sha256((root/name).read_bytes()).hexdigest()!=pin:raise ValueError('Changed source '+name)
 saved=json.loads((root/'complete109_index_unit_tradeoffs107.json').read_text());packets=[x['packet']for x in saved['forms']];old=saved['canonical_parent'];p=packets[0];free=p['polynomial_ledger']['free'];fixed=set(p['fixed_numerals'])
 assert len(p['witnesses'])==24 and all(q['source'][:75]==p['source'][:75]and q['comparisons'][:8]==p['comparisons'][:8]for q in packets)
 core=p['source'][:75];kept=p['comparisons'][:8];assert Counter(r[1]for r in core)==Counter({'*':40,'+':24,'-':11})
 env=execute(core,{x:P(x)for x in free});oe=execute(old['source'],{x:P(x)for x in free});get=lambda e,x:P(x)if type(x)is int else e[x]
 oldres=[get(oe,a)-get(oe,b)for a,b in old['comparisons']]
 indices=(3,7,12,9,5)
 for j,(port,i)in enumerate(zip(PORTS,indices)):assert oldres[i]==((1-env[port])if j==0 else(env[port]-1))
 retained=[r for i,r in enumerate(oldres)if i not in indices]
 assert retained==[get(env,a)-get(env,b)for a,b in kept]
 degree=lambda poly:max((sum(x not in fixed for x in mon)for mon in poly),default=-1)
 def top(poly):
  D=degree(poly);return {mon:c for mon,c in poly.items()if sum(x not in fixed for x in mon)==D}
 b,w,s,J,a,ga,c,dlt,i,j,h,g,eta,zeta=[P(x)for x in('Bm1','w','s','Jrep','a','ga','c','delta','i','j','h','tau_gap','eta','zeta')]
 k=eta+zeta;dt=b*w*J+4*ga*a;mt=dt**2+2*a*c*dt
 Delta=a*a+4*a+3;rr=P('r');yy=P('y_aux')
 assert env['A']==Delta
 assert env['main_unit']==env['R14']**2-Delta*c**2
 assert env['input_unit']==env['exponent_rhs']**2-Delta*env['index_rhs']**2
 assert env['aux_unit']==(i*c**2)**2*((j*c-rr)**2-yy**2)+yy**2
 assert env['first_unit']==g*g+env['wn2']*env['sn2']**2*k*(2*g-k)
 assert env['index_unit']==k-rr-h*env['wn2']*env['sn2']
 leaders=[b**7*w*s**2*k*J**7*(2*g-k),mt,-4*dlt**2*a**5,i**2*j**2*c**6,-h*w*s*b**4*J**4]
 assert [degree(env[x])for x in PORTS]==list(DEGREES)
 assert [top(env[x])for x in PORTS]==leaders
 assert max(map(degree,retained))<=6
 allparts=list(partitions(5));assert len(allparts)==52 and len(set(allparts))==52
 valid=[part for part in allparts if not any(0 in block and 4 in block for block in part)];assert len(valid)==37
 assert Counter(map(len,valid))==Counter({2:8,3:19,4:9,5:1})
 records=[];totalgates=0;unitchecks=0
 for part in valid:
  gcount=len(part);rows,pairs,out,cert=emit(core,kept,part);ledger=inspect(rows,free,out);assert ledger==dict(operations=103+2*gcount,M=53,A=50+2*gcount)
  assert cert==80-gcount and len(pairs)==8+gcount;totalgates+=len(rows)
  ds=[sum(DEGREES[x]for x in block)for block in part];D=2*max(ds)
  records.append(dict(partition=[[LABELS[x]for x in block]for block in part],groups=gcount,group_degrees=ds,exact_degree=D,ledger=ledger))
  # Independent abstract arithmetic truth table; the written integer-unit
  # theorem, not this finite box, establishes the unrestricted implication.
  for values in itertools.product(range(-2,3),repeat=5):
   if any(values[x]==-1 for x in(1,2,3)):continue
   grouped=all(math.prod(values[x]for x in block)==1 for block in part)
   assert grouped==(values==(1,1,1,1,1));unitchecks+=1
 points=sorted({(r['ledger']['operations'],r['exact_degree'])for r in records})
 frontier=[pt for pt in points if not any(q!=pt and q[0]<=pt[0]and q[1]<=pt[1]for q in points)]
 assert frontier==[(107,42),(109,28),(111,24)]
 winners=[dict(operations=o,degree=D,partitions=[r['partition']for r in records if r['ledger']['operations']==o and r['exact_degree']==D])for o,D in frontier]
 assert [len(x['partitions'])for x in winners]==[1,1,2]
 target=((0,),(1,3),(2,4));rows,pairs,out,cert=emit(core,kept,target);full=execute(rows,{x:P(x)for x in free});F=full[out]
 residuals=[get(full,x)-get(full,y)for x,y in pairs];assert [degree(x)for x in residuals][-3:]==[12,14,14]
 expectedleader=(i**2*j**2*c**6*mt)**2+(4*b**4*h*w*s*J**4*dlt**2*a**5)**2
 assert degree(F)==28 and top(F)==expectedleader
 independentfull=sum((r*r for r in retained),P())+(env[PORTS[0]]-1)**2+(env[PORTS[1]]*env[PORTS[3]]-1)**2+(env[PORTS[2]]*env[PORTS[4]]-1)**2
 assert F==independentfull
 parentfull=sum((r*r for r in oldres),P());correction=sum(((mathprod-1)**2 for mathprod in(env[PORTS[0]],env[PORTS[1]]*env[PORTS[3]],env[PORTS[2]]*env[PORTS[4]])),P())-sum(((env[x]-1)**2 for x in PORTS),P())
 assert F-parentfull==correction
 unique=tuple(sorted(['ga']*4+['a']*4+['i']*4+['j']*4+['c']*12));assert F[unique]==256
 mod4=0
 for aa,dd,cc in itertools.product(range(4),repeat=3):
  Delta=aa*aa+4*aa+3;assert(dd*dd-Delta*cc*cc)%4!=3;mod4+=1
 for tt,U,y in itertools.product(range(4),repeat=3):assert(tt*tt*(U*U-y*y)+y*y)%4!=3;mod4+=1
 return dict(status='PASS',pins=PINS,unit_order=list(LABELS),unit_exact_degrees=list(DEGREES),unit_highest_forms=[[[list(mon),coef]for mon,coef in sorted(poly.items())]for poly in leaders],counts=dict(all_set_partitions=52,separated_partitions=37,complete_schedules_recounted=37,live_paid_gates=totalgates,abstract_integer_cases=unitchecks,mod4_cases=mod4,actual_unit_residual_identities=5,actual_retained_residual_identities=8,literal_norm_definitions=4,literal_index_definition=1,discriminant_identity=1),partitions=records,frontier=winners,degree28=dict(source=rows,comparisons=pairs,output=out,ledger=inspect(rows,free,out),witnesses=p['witnesses'],fixed_numerals=p['fixed_numerals'],all_residual_degrees=[degree(x)for x in residuals],full_polynomial_terms=len(F),full_polynomial_sha256=hashlib.sha256(json.dumps([[list(m),v]for m,v in sorted(F.items())],separators=(',',':')).encode()).hexdigest(),highest_homogeneous_polynomial=[[list(mon),coef]for mon,coef in sorted(expectedleader.items())],universal_nonzero_monomial=list(unique),universal_nonzero_coefficient=256),scope='Independent source-based math/count review of the37 partitions that separate N0 and Nk. General integer sign theorem; exact degree28 full coefficient proof. No author census/API execution, no claim about the15 excluded actual partitions, no global optimality or new input theorem.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--output',required=True);ap.add_argument('--expect');a=ap.parse_args();out=verify(a.root)
 if a.expect and not exact(out,json.loads(Path(a.expect).read_text())):raise ValueError('Saved receipt mismatch')
 Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'counts':out['counts'],'frontier':out['frontier']},sort_keys=True))
if __name__=='__main__':main()
