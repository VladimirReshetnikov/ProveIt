#!/usr/bin/env python3
"""Independent exact finite audit; imports no incoming program.
The mathematical unbounded source/ratio dependencies are not tested here.
"""
import ast, collections, gzip, hashlib, itertools, json
from pathlib import Path
HERE=Path(__file__).resolve().parent
S=HERE.parent/'review/sources'
P=S/'ZFC_Diophantine_Degree_Separated_2026-10-23/ZFC_Diophantine_Degree_Separated'
Q=S/'ConZFC_Separated_Degrees_2026-10-23/con-zfc-separated-degrees-2026-10-23'
def require(t,s):
 if not t:raise ValueError(s)
def load(p):return json.loads(p.read_text())
def add(p,q,scale=1):
 r=collections.Counter(p)
 for x,c in q.items():r[x]+=scale*c
 return {x:c for x,c in r.items() if c}
def mul(p,q):
 r=collections.Counter()
 for x,c in p.items():
  for y,d in q.items():r[tuple(a+b for a,b in zip(x,y))]+=c*d
 return {x:c for x,c in r.items() if c}
def read_parent(path):
 s=load(path);names=s['variables']+s['constants'];z=(0,)*len(names)
 def visit(t):
  if isinstance(t,ast.Constant) and type(t.value)==int:return {z:t.value} if t.value else {}
  if isinstance(t,ast.Name):
   if t.id in s['affine_abbreviations']:return parse(s['affine_abbreviations'][t.id])
   k=list(z);k[names.index(t.id)]=1;return {tuple(k):1}
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return {x:-v for x,v in visit(t.operand).items()}
  if isinstance(t,ast.BinOp):
   if isinstance(t.op,ast.Add):return add(visit(t.left),visit(t.right))
   if isinstance(t.op,ast.Sub):return add(visit(t.left),visit(t.right),-1)
   if isinstance(t.op,ast.Mult):return mul(visit(t.left),visit(t.right))
   if isinstance(t.op,ast.Pow):
    require(isinstance(t.right,ast.Constant) and type(t.right.value)==int and 0<=t.right.value<=4,'power grammar')
    r={z:1}
    for _ in range(t.right.value):r=mul(r,visit(t.left))
    return r
  raise ValueError('source polynomial grammar')
 def parse(t):return visit(ast.parse(t.replace('^','**'),mode='eval').body)
 out=[]
 for r in s['equations']:
  terms={tuple(t['powers']):t['coefficient'] for t in r['terms']}
  require(terms==parse(r['residual']),'residual and sparse terms disagree')
  out.append(terms)
 return s,out

def extract(rows,w,q):
 n=len(w);require(len(set(w))==n,'variable label collision')
 expansions={0:[()],1:[(i,) for i in range(n)],2:list(itertools.combinations_with_replacement(range(n),2))}
 kernels=[{} for _ in range(3)];pieces=[]
 for j,row in enumerate(rows):
  grouped={}
  for mon,c in row.items():
   coord=tuple(i for i,e in enumerate(mon[:n]) for _ in range(e));pp=mon[n:]
   grouped.setdefault(coord,{})[pp]=c
  for coord,coeff in grouped.items():
   d=len(coord);require(d<=2,'nonquadratic source');e=q[j]-sum(w[i] for i in coord)
   require(e>=0,'negative reversed exponent');fac=1 if d==2 and coord[0]!=coord[1] else 2
   weighted={pp:fac*c for pp,c in coeff.items()}
   require(e not in kernels[d],'kernel exponent collision')
   kernels[d][e]=weighted;pieces.append((j,coord,e,weighted))
 targets={t:j for j,t in enumerate(q)};require(len(targets)==len(q),'duplicate target')
 received=[{} for _ in rows];checks=0;hits=0
 for j,coord,e,co in pieces:
  for expanded in expansions[len(coord)]:
   checks+=1;t=e+sum(w[i] for i in expanded)
   if t in targets:
    require(targets[t]==j and expanded==coord,'target alias')
    hits+=1;alpha=[0]*n
    for i in expanded:alpha[i]+=1
    fac=2 if len(expanded)==2 and expanded[0]!=expanded[1] else 1
    received[j]=add(received[j],{tuple(alpha)+pp:fac*c for pp,c in co.items()})
 for a,b in zip(received,rows):require(a=={x:2*c for x,c in b.items()},'extraction identity')
 return kernels,{'interactions':checks,'records':hits,'kernel_degrees':[max(k) for k in kernels],'W':max(w),'Q':max(q)}

def audit_sources():
 s,rows=read_parent(P/'encoding/parent_source.json');s2,rows2=read_parent(Q/'data/parent_quartic31.json')
 require(rows==rows2 and s['variables']==s2['variables'],'parent sources differ')
 code=load(P/'encoding/split_code.json');rr=list(rows)
 rr[13]=add(rows[13],rows[1]);rr[14]=add(rows[14],rows[2]);require(add(rr[13],rr[1],-1)==rows[13] and add(rr[14],rr[2],-1)==rows[14],'inverse row identity')
 targets=[0]*22
 for row,t in zip(code['order'],code['targets']):targets[row-1]=t
 kk,result=extract(rr,code['weights'],targets)
 stated=load(P/'encoding/split_kernels.json')['kernels']
 for d in range(3):
  actual={t['exponent']:{tuple(c['powers']):c['coefficient'] for c in t['coefficient']} for t in stated[d]['terms']}
  require(kk[d]==actual,'published split kernel differs')
 require(kk[2][1929]=={(0,0,0,0):1},'positive leading kernel')
 result['H']=max(v+d*result['W'] for d,v in enumerate(result['kernel_degrees']))
 c=load(Q/'data/channel_certificate108.json');kk2,r2=extract(rows,c['weights'],c['target_by_equation'])
 channels=load(Q/'data/degree_channels.json')['channels']
 for d in range(3):
  actual={t['exponent']:{tuple(c['powers']):c['coefficient'] for c in t['recipe']} for t in channels[str(d)]}
  require(kk2[d]==actual,'published channel kernel differs')
 r2['H_with_carrier']=c['Q']+1+2*c['W']
 return {'split116':result,'channels108':r2}

def audit_nine():
 a=P/'nine_free_adjunct';c=load(a/'generated/split_116_positive.json');d=load(a/'generated/split_116_positive_certificate.json')
 ports=[];binding=load(a/'coefficients/old_tuple/COEFFICIENT_BINDING.json')
 for f in binding['payloads']:
  raw=gzip.decompress((a/'coefficients/old_tuple'/f['path']).read_bytes())
  require(hashlib.sha256(raw).hexdigest()==f['sha256'],'fixed payload hash');v=int.from_bytes(raw,'little');require(v.bit_length()==f['bit_length'],'fixed payload bits');ports.append(v)
 def fixed(poly,p):
  values={t['name']:sum(t2['coefficient']*prod(pow(v,e,p) for v,e in zip(ports,t2['powers'])) for t2 in t['terms'])%p for t in poly['coefficient_recipes']}
  values['base_scale']=pow(2,poly['base_scale_exponent'],p);values['threshold_scale']=pow(2,poly['threshold_scale_exponent'],p)
  return values
 def run(poly,p):
  f=fixed(poly,p);pairs=[];counts=collections.Counter();used=set()
  def scan(i):
   if i in used:return
   used.add(i);node=poly['nodes'][i]
   if node['kind'] in ('add','sub','mul'):scan(node['left']);scan(node['right'])
  scan(poly['output']);require(len(used)==len(poly['nodes']),'dead node')
  for idx,t in enumerate(poly['nodes']):
   k=t['kind']
   if k=='variable':pairs.append((1,1))
   elif k=='literal':pairs.append((0,t['value']%p))
   elif k=='fixed':pairs.append((0,f[t['name']]))
   else:
    require(k in ('add','sub','mul') and t['left']<idx and t['right']<idx,'DAG grammar');counts[k]+=1
    x,h=pairs[t['left']];y,j=pairs[t['right']]
    if k=='mul':pairs.append((x+y,h*j%p))
    else:
     degree=max(x,y);pairs.append((degree,((h if x==degree else 0)+(1 if k=='add' else -1)*(j if y==degree else 0))%p))
  return counts,pairs[poly['output']]
 def eval_dag(poly,p,inputs):
  f=fixed(poly,p);v=[]
  for t in poly['nodes']:
   k=t['kind']
   if k=='variable':x=inputs[t['name']]
   elif k=='literal':x=t['value']
   elif k=='fixed':x=f[t['name']]
   else:
    a1,b1=v[t['left']],v[t['right']];x=a1+b1 if k=='add' else a1-b1 if k=='sub' else a1*b1
   v.append(x%p)
  return v[poly['output']]
 results=[]
 for prime in [101,1009,1000003]:
  counts,pair=run(c,prime);counts2,dpair=run(d,prime)
  require(sum(counts.values())==473 and dict(counts)==c['operation_counts'],'operation ledger')
  require(dpair[0]==1910404 and dpair[1]!=0,'degree witness')
  for k in range(21):
   inputs={v:((k+2)**(i+1)+7*i)%prime for i,v in enumerate(c['variables'])}
   require(eval_dag(c,prime,inputs)==eval_dag(d,prime,inputs),'certificate modular replay')
  results.append({'prime':prime,'degree':dpair[0],'diagonal_leader':dpair[1]})
 return {'live_operations':473,'operation_counts':dict(counts),'degree_witnesses':results,'modular_replays':63,'scope':'Exact degree applies to cancellation-resolved certificate; written universal norm identity links the main DAG. Modular replay corroborates but does not itself prove that identity.'}
def prod(xs):
 x=1
 for v in xs:x*=v
 return x
if __name__=='__main__':
 receipt={'status':'PASS','sources':audit_sources(),'nine':audit_nine(),'scope':'Independent finite reconstruction and literal DAG audit. Unbounded compiler, source equivalence, and number-theoretic semantics remain mathematical dependencies.'}
 print(json.dumps(receipt,indent=2))
 (HERE/'INDEPENDENT_SOURCE_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
