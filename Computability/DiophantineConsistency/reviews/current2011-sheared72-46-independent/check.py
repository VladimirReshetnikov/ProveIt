#!/usr/bin/env python3
"""Independent shear and finite-difference degree review; no Lean."""
import hashlib,json,gzip,collections,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-sheared72-46-candidate';O=D/'research/current2011-ordinary71-60-candidate';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();prime=1000000007
assert sha(P/'polynomial.json')=='cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f' and sha(O/'polynomial.json')=='3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27'
g=json.loads((P/'polynomial.json').read_text());o=json.loads((O/'polynomial.json').read_text());assert g['parent_graph_sha256']==sha(O/'polynomial.json') and g['witnesses']==o['witnesses'] and g['fixed_numerals']==o['fixed_numerals'] and g['coefficient_binding']==o['coefficient_binding'] and g['witness_domain']==o['witness_domain']
new=[['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux']];assert g['source'][:55]==o['source'][:55] and g['source'][55:61]==new and g['source'][61:]==o['source'][60:]
assert not any('y' in row[2:] for row in o['source'][:55]+o['source'][60:])
# Universal identity A*(V²-(V+y)²)+(V+y)² = (V+y)²-A*y*(2V+y).
def add(a,b,s=1):
 c=collections.Counter(a)
 for k,v in b.items():c[k]+=s*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c=collections.Counter()
 for x,u in a.items():
  for y,v in b.items():c[tuple(x[i]+y[i] for i in range(3))]+=u*v
 return {k:v for k,v in c.items() if v}
V={(1,0,0):1};Y={(0,1,0):1};A={(0,0,1):1};old=add(V,Y);old2=mul(old,old);left=add(mul(A,add(mul(V,V),old2,-1)),old2);right=add(old2,mul(A,mul(Y,add(old,V))),-1);assert left==right and left!=add(old2,mul(A,mul(Y,add(old,V))),1)
ports={};assert g['coefficient_binding']['path']=='../fourteen-nonzero-spheres/coefficients/'
for n,m in g['coefficient_binding']['ports'].items():
 f=(P/g['coefficient_binding']['path']/m['file']).resolve();z=f.read_bytes();raw=gzip.decompress(z);assert hashlib.sha256(z).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==m['bits'];ports[n]=int.from_bytes(raw,'big')%prime
w=g['witnesses'];deg={n:1 for n in w};deg.update({n:0 for n in ports});edges={};counts=collections.Counter();rows={r[0]:r for r in g['source']};shape={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']};assert all(rows[k]==v for k,v in shape.items())
for n,op,a,b in g['source']:
 assert n not in deg and op in ('+','-','*') and all(type(x)==int or x in deg for x in (a,b));u=0 if type(a)==int else deg[a];v=0 if type(b)==int else deg[b];deg[n]=u+v if op=='*' else max(u,v)
 if n=='N1':
  assert (deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1);deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
 edges[n]=(a,b);counts[op]+=1
seen=set();leaves=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in edges:
  if n not in seen:seen.add(n);todo.extend(edges[n])
 elif isinstance(n,str):leaves.add(n)
assert len(seen)==len(g['source'])==g['operations']==72 and leaves==set(w+g['fixed_numerals']) and dict(counts)=={'*':38,'+':20,'-':14} and deg[g['output']]==46
# Evaluate the full graph at 0..46 on the diagonal. The 46th finite
# difference equals 46! times the leading coefficient of a degree-≤46 poly.
values=[]
for t in range(47):
 e={n:t for n in w};e.update(ports)
 for n,op,a,b in g['source']:
  x=a if type(a)==int else e[a];y=b if type(b)==int else e[b];e[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 values.append(e[g['output']])
for _ in range(46):values=[(values[i+1]-values[i])%prime for i in range(len(values)-1)]
lead=values[0]*pow(math.factorial(46),-1,prime)%prime;assert lead==110098480
print(json.dumps({'status':'PASS_EXTERNAL_SHEAR_GRAPH','operations':72,'counts':dict(counts),'degree_upper':46,'degree_lower':46,'diagonal_leading_mod_1000000007':lead,'scope':'Exact ring identity and fixed-byte degree; strict-positivity bridge and iPRA transfer not proved.'},indent=2,sort_keys=True))
