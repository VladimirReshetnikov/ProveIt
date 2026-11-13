from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta84-unshift-T-signed-full-zero');raw=Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_bytes()
assert sha256(raw).hexdigest()=='ce50ab07246ad3fb77ad787fa5703fd64a8dfd94a346308b73f891225cb36f03'
g=json.loads(raw);assert [x for x in g['source'] if 'T' in x]==[['T','+','n_T',1],['g74','*','T','c']]
rows=[]
for row in g['source']:
 if row==['T','+','n_T',1]:continue
 rows.append(['n_T' if x=='T' else x for x in row])
assert len(rows)==84
child={'name':'eta/zeta-natural T-unshift signed-port boundary; not a zero-equivalence claim','domain':g['domain'],'witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],'source':rows,'output':g['output'],'parent_sha256':sha256(raw).hexdigest()}
encoded=(json.dumps(child,indent=2,ensure_ascii=False)+'\n').encode()
if '--write' in sys.argv:(D/'probe.json').write_bytes(encoded)
else:assert (D/'probe.json').read_bytes()==encoded
# Exact integer polynomials in K0 and MF; beta=-1, MC=2.
zero=(0,0)
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({zero:x})
K=P({(1,0):1});MF=P({(0,1):1})
w=[1,0,0,2,2,0,0,0,0,1,0,1,0];ports=[-1,K,2,MF]
def eval_graph(graph):
 d={n:pol(v) for n,v in zip(graph['witnesses'],w)};d.update({n:pol(v) for n,v in zip(graph['fixed_numerals'],ports)})
 for name,op,x,y in graph['source']:
  x=d[x] if isinstance(x,str) else pol(x);y=d[y] if isinstance(y,str) else pol(y)
  d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
a=eval_graph(child);b=eval_graph(g)
for key,value in [('q',0),('Y',0),('U',0),('c',1),('kbase',1),('R',0),('Z',-1),('A0',0),('A1',0),('Q',9),('I',3),('g72',0),('V',-1),('Fa',1),('out',0)]:assert a[key]==value,key
assert b['V']==3 and b['Fa']==73 and b['out']==72
print(json.dumps({'parent_sha256':sha256(raw).hexdigest(),'child_sha256':sha256(encoded).hexdigest(),'child_rows':84,'all_rows_exactly_evaluated_over_Z_K0_MF':True,'witness':w,'ports':['-1','K0','2','MF'],'child_output':0,'parent_same_tuple_output':72,'compact_ports_covered':False,'existential_zero_equivalence_refuted':False,'lean_executed':False},sort_keys=True,indent=2))
