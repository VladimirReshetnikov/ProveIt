#!/usr/bin/env python3
"""Explicit polynomial graphs for triangular Pell orientation.

All contractions are acyclic unit substitutions. No exponentiation oracle or
unfixed coefficient occurs in a graph. Use the retained proof for semantics.
"""
from pathlib import Path
import json,hashlib,math,sys
ROOT=Path(__file__).resolve().parent
P=1000000007
def load(p):return json.loads(Path(p).read_text())
def enc(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def build(cert):
 source_name=cert.get('source_file','source206.json')
 literal_limit=cert.get('literal_limit')
 raw=(ROOT/source_name).read_bytes();src=json.loads(raw);pool=load(ROOT/'factored_pool.json');rows=src['residuals'];n=len(src['variables'])
 defs={};used=set()
 for s in cert['steps']:
  r,v=s['row'],s['variable'];ts=rows[r]['terms']
  cs=[c for c,m in ts if m==[v]]
  if v in defs or r in used or len(cs)!=1 or abs(cs[0])!=1 or any(v in m for c,m in ts if m!=[v]):raise ValueError('invalid unit pivot')
  defs[v]=(r,[[-cs[0]*c,m] for c,m in ts if m!=[v]]);used.add(r)
 inputs=[i for i in range(n) if i not in defs];nodes=[['var',i] for i in range(len(inputs))];roots=dict(zip(inputs,range(len(inputs))));cache={tuple(a):i for i,a in enumerate(nodes)};blocks=[];busy=set();constant_roots={}
 def const(c):
  if c in constant_roots:return constant_roots[c]
  if literal_limit is None or abs(c)<=literal_limit:out=node('const',c)
  elif c<0:out=node('-',const(0),const(-c))
  else:
   q,r=divmod(c,256);out=node('*',const(q),const(256))
   if r:out=node('+',out,const(r))
  constant_roots[c]=out;return out
 def node(op,*a):
  if op in ('+','*'):a=tuple(sorted(a))
  if op in ('+','-','*'):
   i,j=a;ci=nodes[i][1] if nodes[i][0]=='const' else None;cj=nodes[j][1] if nodes[j][0]=='const' else None
   if ci is not None and cj is not None:
    value=ci+cj if op=='+' else ci-cj if op=='-' else ci*cj
    if literal_limit is None or abs(value)<=literal_limit:return const(value)
   if op=='+' and ci==0:return j
   if op=='+' and cj==0:return i
   if op=='-' and cj==0:return i
   if op=='-' and i==j:return const(0)
   if op=='*' and (ci==0 or cj==0):return const(0)
   if op=='*' and ci==1:return j
   if op=='*' and cj==1:return i
  key=(op,*a)
  if key not in cache:cache[key]=len(nodes);nodes.append(list(key))
  return cache[key]
 def total(xs):
  if not xs:return const(0)
  z=xs[0]
  for x in xs[1:]:z=node('+',z,x)
  return z
 def product(xs):
  if not xs:return const(1)
  z=xs[0]
  for x in xs[1:]:z=node('*',z,x)
  return z
 def expression(ts,registers):
  # Keep arithmetic sharing inside each independently verifiable expression.
  # Constants remain shared; source-coordinate roots are explicit ports.
  for key in list(cache):
   if key[0] not in ('const','var'):del cache[key]
  pos=[];neg=[]
  for c,m in ts:
   if not c:continue
   z=product([registers[j] for j in m]);z=node('*',const(abs(c)),z)
   (pos if c>0 else neg).append(z)
  if not neg:return total(pos)
  return node('-',total(pos),total(neg))
 def define(v):
  if v in roots:return roots[v]
  if v in busy:raise ValueError('cyclic definition')
  busy.add(v);r,ts=defs[v]
  for c,m in ts:
   for j in m:define(j)
  roots[v]=expression(ts,roots);blocks.append({'kind':'definition','source_row':r,'source_variable':v,'root':roots[v]});busy.remove(v);return roots[v]
 for v in sorted(defs):define(v)
 residual=[];kept=[]
 for r,row in enumerate(rows[:-1]):
  if r not in used:
   out=expression(row['terms'],roots);residual.append(out);kept.append(r);blocks.append({'kind':'residual','source_row':r,'root':out})
 # The large last polynomial is specified by five short literal blocks.
 Ts=[];Es=[];bs=[]
 for i,b in enumerate(pool['blocks']):
  d={}
  for field in ('base','T','E'):
   d[field]=expression(b[field],roots);blocks.append({'kind':'pool_macro','block':i,'field':field,'root':d[field]})
  bs.append(d['base']);Ts.append(d['T']);Es.append(d['E'])
 for key in list(cache):
  if key[0] not in ('const','var'):del cache[key]
 pieces=[product([bs[i],Es[i]]+Ts[:i]+Ts[i+1:]) for i in range(5)]
 out=node('-',total(pieces),product([roots[pool['pool_coordinates'][0]]]+Ts));residual.append(out);kept.append(len(rows)-1);blocks.append({'kind':'pool','source_row':len(rows)-1,'root':out})
 for key in list(cache):
  if key[0] not in ('const','var'):del cache[key]
 output=total([node('*',r,r) for r in residual])
 # A weighted highest-homogeneous specialization certifies the exact degree.
 dd={i:1 for i in inputs};tt={i:(i+3)%P for i in inputs};hh={i:0 for i in inputs}
 def stat(ts):
  ds=[sum(dd[j] for j in m) for c,m in ts];d=max(ds,default=0)
  top=sum(c*math.prod(tt[j] for j in m) for (c,m),d0 in zip(ts,ds) if d0==d)%P
  hs=[(abs(c)-1).bit_length()+sum(hh[j] for j in m) for c,m in ts if c]
  h=max(hs,default=0)+(len(hs)-1).bit_length() if hs else 0
  return d,top,h
 for b in blocks:
  if b['kind']=='definition':
   v=b['source_variable'];dd[v],tt[v],hh[v]=stat(defs[v][1])
 rd=[];tops=[];hs=[]
 for r in kept:
  d,t,h=stat(rows[r]['terms']);rd.append(d);tops.append(t);hs.append(h)
 D=max(rd);w=next((i for i,(d,t) in enumerate(zip(rd,tops)) if d==D and t),None)
 if w is None:raise ValueError('leading specialization failed; choose a different direction')
 live=set();todo=[output]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0] in ('+','-','*'):todo.extend(nodes[i][1:])
 # Check actual input occurrence independently by a generic Jacobian evaluation.
 # Derivative evidence is emitted below; verifier recalculates it directly.
 def differentiate(mod,offset):
  vals=[];grads=[];directions=[(i+offset)*(i+offset+1)%mod for i in inputs]
  for nd in nodes:
   op=nd[0]
   if op=='var':
    vals.append(directions[nd[1]]);g=[0]*len(inputs);g[nd[1]]=1;grads.append(g)
   elif op=='const':vals.append(nd[1]%mod);grads.append([0]*len(inputs))
   else:
    a,b=nd[1:];va,vb=vals[a],vals[b];ga,gb=grads[a],grads[b]
    if op=='+':vals.append((va+vb)%mod);grads.append([(x+y)%mod for x,y in zip(ga,gb)])
    elif op=='-':vals.append((va-vb)%mod);grads.append([(x-y)%mod for x,y in zip(ga,gb)])
    else:vals.append(va*vb%mod);grads.append([(x*vb+y*va)%mod for x,y in zip(ga,gb)])
  return directions,grads[output]
 seen=[False]*len(inputs);dc=[]
 for offset in (2,7,23,61):
  point,deriv=differentiate(P,offset);dc.append({'modulus':P,'point':point,'derivatives':deriv})
  seen=[a or bool(b) for a,b in zip(seen,deriv)]
  if all(seen):break
 if not all(seen):raise ValueError('liveness witness failed')
 metrics={'variables':len(inputs),'residuals':len(residual),'exact_degree':2*D,'binary_operations':sum(nodes[i][0] in ('+','-','*') for i in live),'live_nodes':len(live),'stored_nodes':len(nodes),'largest_literal':max(abs(nodes[i][1]) for i in live if nodes[i][0]=='const'),'coefficient_height_strict_power_of_two':2*max(hs)+(len(hs)-1).bit_length()+1}
 return {'schema':'pell-orientation-polynomial-v1','domain':'unrestricted integers','source_file':source_name,'literal_limit':literal_limit,'source_sha256':hashlib.sha256(raw).hexdigest(),'parent_sha256':hashlib.sha256((ROOT/'parent206.json').read_bytes()).hexdigest(),'variables':[{'source_index':i,**src['variables'][i]} for i in inputs],'source_input_indices':inputs,'source_definitions':cert['steps'],'retained_source_rows':kept,'nodes':nodes,'blocks':blocks,'residual_roots':residual,'output':output,'restore_source_roots':[roots[i] for i in range(n)],'metrics':metrics,'degree_certificate':{'modulus':P,'direction':[i+3 for i in inputs],'source_degrees':[dd[i] for i in range(n)],'source_leading_coefficients':[tt[i] for i in range(n)],'residual_degrees':rd,'residual_leading_coefficients':tops,'witness_source_row':kept[w],'witness_residue':tops[w]},'input_occurrence_certificates':dc}
def main():
 out=ROOT/'equations';out.mkdir(exist_ok=True)
 profiles=[]
 for file in sorted((ROOT/'certificates').glob('*.json')):
  graph=build(load(file));name=f"integer{graph['metrics']['variables']}_degree{graph['metrics']['exact_degree']}";name=('control_' if graph['source_file']=='parent206.json' else '')+name;name+=('_literals'+str(graph['literal_limit']) if graph['literal_limit'] else '');dst=out/(name+'.json');data=enc(graph)
  if '--check' in sys.argv:
   if dst.read_bytes()!=data:raise ValueError('byte reconstruction mismatch '+name)
  else:dst.write_bytes(data)
  profiles.append({'name':name,'certificate':file.name,**graph['metrics']});print(json.dumps(profiles[-1]),flush=True)
 (ROOT/'PROFILES.json').write_bytes(enc(profiles))
if __name__=='__main__':main()
