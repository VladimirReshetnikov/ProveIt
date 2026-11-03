#!/usr/bin/env python3
"""Check complete 73 DAG, exact parent mapping, liveness and modular degree."""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import gzip,json,random,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent;d=h.parents[1];parent=d/'con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json';candidate=h/'candidate.json';payload=d/'research/ten-positive-unshift-t-finite/coefficients'
pins={parent:'8b9b9421ae8a0762725852034b3db6d29b14660b3a4d0587e1494a933b5271c9',candidate:'c83151606214c211993fa0c5b9913abae3b6bcf2b00af107e599e4855f936ca6'}
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
for p,v in pins.items():need(sha(p)==v,'pin mismatch '+str(p))
g=json.loads(parent.read_text());c=json.loads(candidate.read_text());expect=[]
for n,op,a,b in g['source']:
 if n in ('LBt','center'):continue
 expect.append([n,op,'n' if a=='center' else a,'n' if b=='center' else b])
need(c['source']==expect and len(expect)==73,'row mapping')
need(c['witnesses']==g['witnesses'] and c['fixed_numerals']==g['fixed_numerals'] and c['coefficient_binding']==g['coefficient_binding'] and c['output']==g['output'],'metadata')
inputs=set(c['witnesses']+c['fixed_numerals']);available=set(inputs);nodes={};degree={x:1 for x in c['witnesses']};degree.update({x:0 for x in c['fixed_numerals']})
for n,op,a,b in c['source']:
 need(n not in available and op in ('+','-','*'),'duplicate or operation')
 for x in (a,b):need(type(x) is int and x>=0 or isinstance(x,str) and x in available,'bad input')
 da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b];degree[n]=da+db if op=='*' else max(da,db);nodes[n]=(a,b);available.add(n)
seen=set();todo=[c['output']]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n)
 if n in nodes:todo.extend(x for x in nodes[n] if isinstance(x,str))
need(seen==inputs|set(nodes),'dead input or operation')
counts=dict(Counter(r[1] for r in c['source']));need(counts=={'*':43,'+':17,'-':13},'breakdown')
need(degree[c['output']]==352,'structural degree bound')
prime=1000000007;ports={};rawhash={}
for n,info in c['coefficient_binding']['ports'].items():
 raw=gzip.decompress((payload/info['file']).read_bytes());need(sha256(raw).hexdigest()==info['raw_sha256'],'payload '+n)
 ports[n]=int.from_bytes(raw,'little')%prime;rawhash[n]=sha256(raw).hexdigest()
def add(a,b,sgn=1):
 z=[0]*max(len(a),len(b))
 for i,x in enumerate(a):z[i]=(z[i]+x)%prime
 for i,x in enumerate(b):z[i]=(z[i]+sgn*x)%prime
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 while len(z)>1 and z[-1]==0:z.pop()
 return z
env={x:[0,1] for x in c['witnesses']};env.update({n:[v] for n,v in ports.items()})
for n,op,a,b in c['source']:
 x=[a%prime] if type(a)is int else env[a];y=[b%prime] if type(b)is int else env[b]
 env[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
p=env[c['output']];need(len(p)-1==352 and p[-1]!=0,'diagonal leading coefficient')
def eval_rows(rows,vals):
 e=dict(vals)
 for n,op,a,b in rows:
  x=a if type(a)is int else e[a];y=b if type(b)is int else e[b];e[n]=((x*y) if op=='*' else (x+y if op=='+' else x-y))%prime
 return e
rng=random.Random(730352);samples=200
for _ in range(samples):
 val={x:rng.randrange(prime) for x in inputs};v=eval_rows(c['source'],val);lift=dict(val);lift['n']=(val['n']+v['V2']*v['Bt'])%prime;old=eval_rows(g['source'],lift)
 need(old['N']==v['N'] and old['center']==val['n'],'substitution evaluation')
for pth,v in pins.items():need(sha(pth)==v,'final pin changed')
print(json.dumps({'status':'PASS_EXTERNAL_GRAPH_CHECK','operations':len(nodes),'breakdown':counts,'live_inputs':len(inputs),'degree_upper':352,'diagonal_degree':len(p)-1,'diagonal_leading_coefficient_mod_prime':p[-1],'prime':prime,'samples':samples,'coefficient_raw_sha256':rawhash,'scope':'external DAG/liveness/modular degree and finite substitution checks; no model equivalence or file semantics theorem'},sort_keys=True,indent=2))
