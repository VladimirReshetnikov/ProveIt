#!/usr/bin/env python3
"""Generate a sparse quartic candidate, preserving shared graph intermediates."""
import json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];src=D/'research/current2011-ordinary67-94-candidate/polynomial.json';raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb';g=json.loads(raw)
assert len(g['source'])==67 and g['output']==g['source'][-1][0] and len(g['witnesses'])==14 and g['fixed_numerals']==['beta','K0','MC','MF']
N=lambda x:['num',x];V=lambda i:['var',i];add=lambda a,b:['add',a,b];sub=lambda a,b:['sub',a,b];mul=lambda a,b:['mul',a,b];zero=N(0)
# Coordinate zero is Jones's distinguished input. Coordinates 1..14 are
# unrestricted natural witnesses; the graph evaluates their positive shifts.
pairs={n:(add(V(i+1),N(1)),zero,True) for i,n in enumerate(g['witnesses'])};pairs.update({n:([ 'port',n],zero,True) for n in g['fixed_numerals']});nextvar=15;residuals=[];records=[]
def get(x):return (N(x),zero,True) if type(x)==int else pairs[x]
def parts(op,a,b):
 ap,an,_=a;bp,bn,_=b
 if op=='+':return add(ap,bp),add(an,bn)
 if op=='-':return add(ap,bn),add(an,bp)
 assert op=='*';return add(mul(ap,bp),mul(an,bn)),add(mul(ap,bn),mul(an,bp))
for idx,(name,op,a,b) in enumerate(g['source']):
 assert name not in pairs and op in ('+','-','*');x,y=get(a),get(b);positive=op in ('+','*') and x[2] and y[2];ep,en=parts(op,x,y)
 if name==g['output']:
  residuals.append({'kind':'output','gate':name,'expr':sub(ep,en)});records.append({'name':name,'output':True,'op':op,'left':a,'right':b,'known_nonnegative':positive});continue
 p=V(nextvar);nextvar+=1
 if positive:
  # Both negative parts are structurally zero; the simplified expression
  # uses only the nonnegative halves and does not require subtraction.
  ep=add(x[0],y[0]) if op=='+' else mul(x[0],y[0]);residuals.append({'kind':'positive','gate':name,'expr':sub(p,ep)});pairs[name]=(p,zero,True);records.append({'name':name,'op':op,'left':a,'right':b,'known_nonnegative':True,'positive_coordinate':p[1]})
 else:
  n=V(nextvar);nextvar+=1;residuals.extend([{'kind':'positive','gate':name,'expr':sub(p,ep)},{'kind':'negative','gate':name,'expr':sub(n,en)}]);pairs[name]=(p,n,False);records.append({'name':name,'op':op,'left':a,'right':b,'known_nonnegative':False,'positive_coordinate':p[1],'negative_coordinate':n[1]})
guard=nextvar;nextvar+=1;residuals.insert(0,{'kind':'guard','expr':sub(V(guard),N(1))})
assert nextvar==111 and guard==110 and len(residuals)==97
out={'schema':'sharing-quartic-candidate-v1','source_graph':'../current2011-ordinary67-94-candidate/polynomial.json','source_graph_sha256':hashlib.sha256(raw).hexdigest(),'fixed_ports':g['fixed_numerals'],'coefficient_binding':g['coefficient_binding'],'input_coordinate':0,'domain':'coordinates 1..110 range over natural numbers; input coordinate fixed to 1','original_coordinates':{n:i+1 for i,n in enumerate(g['witnesses'])},'positive_shift':1,'guard_coordinate':guard,'coordinate_count':nextvar,'jones_witness_count':nextvar-1,'gate_records':records,'residuals':residuals,'output':'sum of squares of every residual','status':'external candidate; no Lean equivalence or Jones endpoint'}
assert not (P/'seed.json').exists();(P/'seed.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
