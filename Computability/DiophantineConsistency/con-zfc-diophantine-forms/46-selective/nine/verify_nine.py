#!/usr/bin/env python3
"""Independent finite checks of support-selective source, domains and degree.

These do not prove consistency or replace the unbounded arithmetic proof.
"""
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations_with_replacement, product
from math import factorial, isqrt
import gzip, hashlib, json, random

ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF']
PORT_FILES=['beta','K','MC','MF_source']
def require(p,msg):
 if not p: raise ValueError(msg)

def recipe_value(recipe,ports,mod=None):
 total=0
 for t in recipe:
  v=t['coefficient']
  for x,e in zip(ports,t['powers']):v*=pow(x,e,mod) if mod else x**e
  total+=v
 return total%mod if mod else total

def coefficients(obj,ports,mod):
 d={name:recipe_value(rec,ports,mod) for name,rec in obj['coefficient_recipes'].items()}
 d['base_floor']=pow(2,obj['base_floor_exponent'],mod)
 return d

def evaluate(obj,values,ports,mod):
 fixed=coefficients(obj,ports,mod);out=[]
 for n in obj['nodes']:
  k=n['kind']
  if k=='variable':v=values[n['name']]
  elif k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  else:
   a,b=out[n['left']],out[n['right']]
   v=a+b if k=='add' else a-b if k=='sub' else a*b
  out.append(v%mod)
 return out[obj['output']],{k:out[i] for k,i in obj['named_nodes'].items()}

def degree_certificate(obj,ports,mod):
 fixed=coefficients(obj,ports,mod);deg=[];lead=[]
 for n in obj['nodes']:
  k=n['kind']
  if k=='variable':d,c=1,1
  elif k=='literal':d,c=0,n['value']%mod
  elif k=='fixed':d,c=0,fixed[n['name']]
  else:
   a,b=n['left'],n['right']
   if k=='mul':d,c=deg[a]+deg[b],lead[a]*lead[b]%mod
   else:
    d=max(deg[a],deg[b]);x=lead[a] if deg[a]==d else 0;y=lead[b] if deg[b]==d else 0
    c=(x+y if k=='add' else x-y)%mod
  deg.append(d);lead.append(c)
 i=obj['output']
 require(lead[i]!=0,'zero final degree leader')
 return {'prime':mod,'degree':deg[i],'diagonal_leading_coefficient_mod_prime':lead[i],
         'named_degrees':{k:deg[i] for k,i in obj['named_nodes'].items()}}

def finalizer(a0,a1,V0,V1,u,v,m,M,n):
 O=u*m;T=u*(n+M)+v-O*(2*M+V0*V1)
 return (T*T-O*O*(a0+V0*V0*a1))**2-4*O**4*V0*V0*a0*a1

def main():
 layout=json.loads((ROOT/'data/layout.json').read_text());data=json.loads((ROOT/'data/raw_recipes.json').read_text())
 weights=layout['weights'];W=max(weights);targets=layout['targets'];perm=layout['row_permutation']
 require(len(weights)==32 and weights[0]==0 and min(weights[1:])>0,'weight interface')
 sums=defaultdict(list)
 for p in combinations_with_replacement(range(32),2):sums[sum(weights[i] for i in p)].append(p)
 active=set();records=[]
 for slot,j in enumerate(perm):
  for t in data['rows'][j]:
   inds=[i for i,e in enumerate(t['alpha'],1) for _ in range(e)];p=tuple([0]*(2-len(inds))+inds)
   active.add(p);require(sums[sum(weights[i] for i in p)]==[p],'active monomial collision')
   e=targets[slot]-sum(a*w for a,w in zip(t['alpha'],weights[1:]));require(e>=0,'negative exponent')
   records.append((slot,j,e,t,p))
 cross=0
 for slot,j,e,t,p in records:
  for target_slot,target in enumerate(targets):
   hits=sums.get(target-e,[])
   require(hits==([p] if target_slot==slot else []),'cross-target interference')
   cross+=len(sums)
 require(len(set(r[2] for r in records))==len(records),'D coefficients collide')
 top=[r for r in records if r[2]==max(s[2] for s in records)]
 require(len(top)==1 and top[0][2]==targets[-1] and top[0][3]['leaf']==2 and top[0][3]['sign']==1,'D top coefficient')
 objects={}
 for domain in ['positive','natural']:
  for suffix in ['','_degree_certificate']:
   key=domain+suffix;obj=json.loads((ROOT/'generated'/('selective_nine_'+key+'.json')).read_text());objects[key]=obj
   require(len(obj['variables'])==9,'nine variables')
   require(sum(n['kind'] in ('add','sub','mul') for n in obj['nodes'])==obj['total_operations'],'gate count')
   require(obj['source_layout_sha256']==hashlib.sha256((ROOT/'data/layout.json').read_bytes()).hexdigest(),'layout binding')
   require(obj['source_recipes_sha256']==hashlib.sha256((ROOT/'data/raw_recipes.json').read_bytes()).hexdigest(),'recipe binding')
   used=set();todo=[obj['output']]
   while todo:
    i=todo.pop()
    if i in used:continue
    used.add(i);n=obj['nodes'][i]
    if 'left' in n:
     require(n['left']<i and n['right']<i,'gate not topological');todo.extend([n['left'],n['right']])
   require(len(used)==len(obj['nodes']),'dead node')
 obj=objects['positive'];actual=[];payloads=[]
 for name,file in zip(PORTS,PORT_FILES):
  path=ROOT/'coefficients/payloads'/f'{file}.bin.gz';raw=gzip.decompress(path.read_bytes());value=int.from_bytes(raw,'little');actual.append(value)
  payloads.append({'port':name,'file':str(path.relative_to(ROOT)),'raw_sha256':hashlib.sha256(raw).hexdigest(),'bit_length':value.bit_length()})
 H=8*(1+sum(actual))**2;require(H<(1<<2140017),'fixed coefficient bound')
 require(all(abs(recipe_value(rec,actual))<H for rec in data['recipes'].values()),'recipe actual bounds')
 require(all(sum(abs(t['coefficient']) for t in rec)<=8 for rec in data['recipes'].values()),'recipe L1 bound')
 require(all(sum(t['powers'])<=2 for rec in data['recipes'].values() for t in rec),'recipe port degree')
 rng=random.Random(23023175);replays=0;source_checks=0;extractions=0
 for mod in [1000000007,1000000009,2147483647]:
  for _ in range(40):
   vals={n:rng.randrange(1,10000) for n in obj['variables']};ports=[x%mod for x in actual]
   value,named=evaluate(obj,vals,ports,mod);certificate,_=evaluate(objects['positive_degree_certificate'],vals,ports,mod)
   require(value==certificate,'degree certificate differs')
   natural,_=evaluate(objects['natural'],{n:x-1 for n,x in vals.items()},ports,mod)
   require(value==natural,'domain translations differ');replays+=1
   B=named['B'];fixed=coefficients(obj,ports,mod);direct=0
   for slot,j,e,t,p in records:
    co=t['leaf'] if isinstance(t['leaf'],int) else fixed[t['leaf']]
    direct+=t['sign']*co*pow(B,e,mod)
   require(direct%mod==named['Dcode'],'D sparse source transcription')
   require(sum(pow(B,e,mod) for e in targets)%mod==named['targets'],'target transcription')
   source_checks+=1
 for _ in range(16):
  ports=[rng.randrange(1,100) for _ in PORTS];fixed=coefficients(obj,ports,1000000007)
  zs=[rng.randrange(4) for _ in weights[1:]];xs=[z+1 for z in zs]
  C={0:1};C.update({w:x for w,x in zip(weights[1:],xs)});C2=defaultdict(int)
  for a,x in C.items():
   for b,y in C.items():C2[a+b]+=x*y
  D={}
  for slot,j,e,t,p in records:
   co=t['leaf'] if isinstance(t['leaf'],int) else recipe_value(data['recipes'][t['leaf']],ports)
   D[e]=t['sign']*co
  for slot,j in enumerate(perm):
   want=0
   for t in data['rows'][j]:
    co=t['leaf'] if isinstance(t['leaf'],int) else recipe_value(data['recipes'][t['leaf']],ports)
    mult=factorial(2-sum(t['alpha']))
    for a in t['alpha']:mult*=factorial(a)
    require(co%mult==0,'factorial coefficient divisibility')
    v=t['sign']*co//mult
    for x,a in zip(xs,t['alpha']):v*=x**a
    want+=v
   got=sum(co*C2.get(targets[slot]-e,0) for e,co in D.items())
   require(got==2*want,'positive-offset target extraction');extractions+=1
 degrees=[];expected=1152*3*(targets[-1]+3*W+2)+12*W+280
 for mod in [1000000007,1000000009,2147483647]:
  cert=degree_certificate(objects['positive_degree_certificate'],actual,mod)
  require(cert['degree']==expected,'wrong degree')
  require(cert['diagonal_leading_coefficient_mod_prime']==pow(2,2050,mod),'wrong degree leader')
  degrees.append(cert)
 fixtures=0
 for r0,r1,u,m in product(range(1,5),range(1,5),[-3,-1,1,2],[1,2]):
  a0,a1=r0*r0,r1*r1;V0,V1=r0+1,r1+1;M=4;v=2*u
  Z=2*M+V0*V1+r0+V0*r1;n=m*Z-M-v//u
  require(n>=0 and finalizer(a0,a1,V0,V1,u,v,m,M,n)==0,'finalizer completeness');fixtures+=1
 zeros=0
 for a0,a1,u,n in product(range(1,8),range(1,8),[-3,-1,1,2],range(5)):
  require(finalizer(a0,a1,8,8,u,2*u,0,4,n)!=0,'zero margin accepted');zeros+=1
 report={'status':'PASS','maximum_weight':W,'target_maximum':targets[-1],'source_span':targets[-1]+2*W,
  'degree':expected,'positive_operations':obj['total_operations'],'natural_operations':objects['natural']['total_operations'],
  'active_pairs':len(active),'all_pair_multisets':528,'distinct_D_records':len(records),
  'source_replays':source_checks,'circuit_domain_and_certificate_replays':replays,'positive_offset_target_extractions':extractions,
  'finalizer_completeness_fixtures':fixtures,'zero_margin_exclusions':zeros,'port_payloads':payloads,'degree_certificates':degrees,
  'degree_proof':'Certificate polynomial is identically the primary polynomial by the displayed norm expansion in PROOF.md; propagated upper bound and nonzero diagonal coefficient prove exact degree.',
  'limits':'Finite implementation checks. The unbounded solvability equivalence uses the accompanying proof and the cited parent-system and Jones ratio theorems.'}
 (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k not in ['port_payloads','degree_certificates']}))
if __name__=='__main__':main()
