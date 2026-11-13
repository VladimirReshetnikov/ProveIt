#!/usr/bin/env python3
"""Exact graph cut, residue exclusions and fixed-port degree; no Lean."""
import gzip,hashlib,itertools,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def require(x,m):
 if not x:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,v in pins.items():require(sha((r/f).read_bytes())==v,'pin '+f)
def obj(p):return json.loads((r/p).read_bytes())
parent=obj('research/adaptive-first-root-factor87/candidate.json');square=obj('research/adaptive87-four-square-free-positive-ordinate87-36/graph.json');g=obj('research/adaptive87-positive-ordinate-product86/graph.json')
require(g['source_parent_sha256']==pins['research/adaptive-first-root-factor87/candidate.json'],'parent pin')
existing=obj('research/adaptive-direct-ordinate86/candidate.json')
def rename(x):return 'auxPositive' if x=='y' else x
require([rename(n) for n in existing['witnesses']]==g['witnesses'] and existing['fixed_numerals']==g['fixed_numerals'] and existing['output']==g['output'] and [[rename(x) for x in row] for row in existing['source']]==g['source'],'existing direct ordinate graph')
require(g['witnesses']==[('auxPositive' if n=='u' else n) for n in parent['witnesses']] and g['fixed_numerals']==parent['fixed_numerals'],'coordinates')
require(g['source']==[(['y2','*','auxPositive','auxPositive'] if row[0]=='y2' else row) for row in parent['source'] if row[0]!='g78'],'entire product graph edit')
remove={'Fs','F0','F1','g86','g87','g88','P13'};require([x for x in g['source'] if x[0] not in remove]==square['source'][:-8],'same four residual graph')
require(square['witnesses']==g['witnesses'] and square['fixed_numerals']==g['fixed_numerals'],'square leaves')
require(square['source'][-8:]==[['fa_minus','-','Fa',1],['a0_sq','*','A0','A0'],['a1_sq','*','A1','A1'],['fa_sq','*','fa_minus','fa_minus'],['strong_sq','*','g72','g72'],['sum0','+','a0_sq','a1_sq'],['sum1','+','sum0','fa_sq'],['output','+','sum1','strong_sq']],'four-square tail')
rows={};known=set(g['witnesses']+g['fixed_numerals'])
for n,o,a,b in g['source']:
 require(n not in known and o in ('+','-','*') and all(type(x)==int or x in known for x in (a,b)),'topology '+n)
 rows[n]=(o,a,b);known.add(n)
for n,o,a,b in [['Fs','+',1,'g72'],['F0','+',1,'A0'],['F1','+',1,'A1'],['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]:require(rows.get(n)==(o,a,b),'product tail '+n)
seen=set();leaves=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in rows:
  if n not in seen:
   seen.add(n);todo.extend(x for x in rows[n][1:] if isinstance(x,str))
 else:leaves.add(n)
counts={o:sum(row[1]==o for row in g['source']) for o in '*+-'};require(len(seen)==86 and len(g['witnesses'])==13 and set(g['witnesses']+g['fixed_numerals'])<=leaves and counts=={'*':47,'+':21,'-':18},'liveness/census')
# Exhaust the four structural mod-four lemmas for arbitrary integer residues.
for q,z,n in itertools.product(range(4),repeat=3):require((1+z*z-(q**3*(q-1))**2*n)%4!=3,'first')
for u,a,c,v in itertools.product(range(4),repeat=4):require((1+v*v-u*u*(1+(a*a+4*a+3)*c*c))%4!=3,'main')
for a,f,v,y in itertools.product(range(4),repeat=4):
 Q=(a*a+4*a+3)*(f*f-1);require((y*y-Q*(y*y-v*v))%4!=3,'aux')
for a,f,i in itertools.product(range(4),repeat=3):require((1+i*i-(a*a+4*a+3)*(f*f-1))%4!=3,'strong')
ports=obj('candidates/one-page-padding-staircase-carrier65-2011/polynomial.json')['coefficient_binding']['ports'];base=r/'candidates/one-page-padding-staircase-carrier65-2011/coefficients';prime=1000000007;values={}
for n,m in ports.items():
 z=(base/m['file']).read_bytes();raw=gzip.decompress(z);x=int.from_bytes(raw,'big')
 require(sha(z)==m['gzip_sha256'] and sha(raw)==m['raw_sha256'] and len(raw)==m['raw_bytes'] and x.bit_length()==m['bits'],'fixed bytes '+n)
 if n=='beta':require(x==2**(47*2011)-1 and x>0,'beta positive')
 values[n]=x%prime
D={n:1 for n in g['witnesses']};D.update({n:0 for n in g['fixed_numerals']});poly={n:[0,1] for n in g['witnesses']};poly.update({n:[v] for n,v in values.items()})
def arg(x):return poly[x] if isinstance(x,str) else [x%prime]
def norm(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
for n,o,a,b in g['source']:
 x=arg(a);y=arg(b);da=D[a] if isinstance(a,str) else 0;db=D[b] if isinstance(b,str) else 0;D[n]=da+db if o=='*' else max(da,db)
 if o=='*':
  z=[0]*(len(x)+len(y)-1)
  for i,u in enumerate(x):
   for j,v in enumerate(y):z[i+j]=(z[i+j]+u*v)%prime
 else:z=[((x[i] if i<len(x) else 0)+(1 if o=='+' else -1)*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))]
 poly[n]=norm(z)
require(D['Fa']==18 and len(poly['P13'])==57 and poly['P13'][-1]==150469829,'diagonal degree lower bound')
# F0/F1/Fs have identical upstream rows to the prior 87-degree certificate;
# their bounds 15,13,10 are inherited, while Fa's bound 18 is just propagated.
for n in ('F0','F1','Fs'):
 todo=[n]; visited=set();prior={x[0]:tuple(x[1:]) for x in parent['source']}
 while todo:
  x=todo.pop()
  if x in visited or x not in rows:continue
  visited.add(x);require(rows[x]==prior[x],'factor ancestry '+x);todo.extend(z for z in rows[x][1:] if isinstance(z,str))
cert=(r/'research/adaptive-direct-ordinate86/DEGREE-87-PARENT.md').read_text();require('`15+13+13+10=51`' in cert and pins['research/adaptive-first-root-factor87/candidate.json'] in cert,'factor degree reference')
print(json.dumps({'scope':'external graph/mod4/degree check; existential bridge and upper-bound certificate documented separately; no Lean','pins_sha256':sha((d/'pins.json').read_bytes()),'graph_sha256':pins['research/adaptive87-positive-ordinate-product86/graph.json'],'live_gates':len(seen),'counts':counts,'degree_upper_inheriting_15_13_10':15+13+10+D['Fa'],'degree56_coefficient_mod_1000000007':poly['P13'][-1],'mod4_cases':[64,256,256,64],'current_beta_positive':True,'existing_86_graph_exact_rename':True},sort_keys=True,indent=2))
