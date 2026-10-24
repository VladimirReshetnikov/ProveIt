#!/usr/bin/env python3
"""Exact, independent structural audit of projection, padding and CRT interfaces.

This checker does not import or execute build_direct.py.  It verifies local
polynomial identities compositionally in a free commutative expression DAG;
the source's million-degree substituted polynomial need not be expanded.
Its finite claims accompany the unbounded proofs in PREPROCESSING_PROOF.md.
"""
import collections
import hashlib
import json
from pathlib import Path

R=Path(__file__).resolve().parent

def require(condition,label):
 if not condition: raise ValueError(label)

class RingDAG:
 def __init__(self): self.nodes=[];self.index={}
 def intern(self,key):
  if key not in self.index:
   self.index[key]=len(self.nodes);self.nodes.append(key)
  return self.index[key]
 def con(self,n): return self.intern(('c',n))
 def var(self,n): return self.intern(('v',n))
 def add(self,a,b):
  if self.nodes[a][0]=='c' and self.nodes[a][1]==0:return b
  if self.nodes[b][0]=='c' and self.nodes[b][1]==0:return a
  if self.nodes[a][0]==self.nodes[b][0]=='c':return self.con(self.nodes[a][1]+self.nodes[b][1])
  return self.intern(('a',*sorted((a,b))))
 def mul(self,a,b):
  if self.nodes[a]==('c',0) or self.nodes[b]==('c',0):return self.con(0)
  if self.nodes[a]==('c',1):return b
  if self.nodes[b]==('c',1):return a
  if self.nodes[a][0]==self.nodes[b][0]=='c':return self.con(self.nodes[a][1]*self.nodes[b][1])
  return self.intern(('m',*sorted((a,b))))
 def sum(self,seq):
  out=self.con(0)
  for value in seq:out=self.add(out,value)
  return out
 def product(self,seq):
  out=self.con(1)
  for value in seq:out=self.mul(out,value)
  return out
 def positive_poly(self,terms,env):
  require(all(t['coefficient']>=0 for t in terms),'nonnegative polynomial')
  return self.sum(self.product([self.con(t['coefficient'])]+[env[x] for x in t['monomial']]) for t in terms)
 def split_poly(self,terms,env):
  return tuple(self.positive_poly([{'coefficient':abs(t['coefficient']),'monomial':t['monomial']}
                                for t in terms if (t['coefficient']>0)==positive],env)
               for positive in (True,False))
 def iadd(self,p,q):return self.add(p[0],q[0]),self.add(p[1],q[1])
 def imul(self,p,q):
  return self.add(self.mul(p[0],q[0]),self.mul(p[1],q[1])),self.add(self.mul(p[0],q[1]),self.mul(p[1],q[0]))
 def isum(self,seq):
  out=(self.con(0),self.con(0))
  for pair in seq:out=self.iadd(out,pair)
  return out
 def iproduct(self,seq):
  out=(self.con(1),self.con(0))
  for pair in seq:out=self.imul(out,pair)
  return out
 def sos(self,seq):return self.isum(self.imul(p,p) for p in seq)
 def load(self,nodes,environment):
  values=[]
  for i,node in enumerate(nodes):
   require(node[0] in ('c','v','a','m'),'natural DAG opcode')
   if node[0]=='c':
    require(node[1]>=0,'natural constant');value=self.con(node[1])
   elif node[0]=='v':value=environment[node[1]]
   else:
    require(0<=node[1]<i and 0<=node[2]<i,'DAG topology')
    value=(self.add if node[0]=='a' else self.mul)(values[node[1]],values[node[2]])
   values.append(value)
  return values

horn=json.loads((R/'horn_shared_source.json').read_text())
row=json.loads((R/'row_source.json').read_text())
circuit=json.loads((R/'circuit.json').read_text())
source=circuit['source_binding']
ring=RingDAG()
expected_names=['N','x','y','M0','i','a','b','c','d',
                'x.i.remainder','x.i.quotient',
                'x.next.remainder','x.next.quotient']
require(row['variables']==expected_names,'eight-column row interface')
rv=ring.load(row['nodes'],[ring.var(('row',i)) for i in range(13)])
rowvars={name:ring.var(('row',i)) for i,name in enumerate(expected_names)}
branches={b['name']:b for b in row['branch_projection']}
require(set(branches)=={b['name'] for b in horn['branches']},'all twelve rules')
projected=[]
for old in horn['branches']:
 b=branches[old['name']];name=old['name']
 env={key:rv[value] for key,value in b['bindings'].items()}
 for key in horn['base_witnesses']:require(env[key]==rowvars[key],name+' base parameter')
 if name=='mp':
  require(env['p']==rowvars['a'] and env['v']==rowvars['b'],'modus ponens reparametrization')
 elif name=='gen':require(env['p']==rowvars['b'],'generalization reparametrization')
 else:require(env['p']==env['q']==ring.con(0),name+' null premises')
 defined=set(horn['base_witnesses'])|{'p','q','v'}
 for j,w in enumerate(old['wires']):
  require(all(t['coefficient']>0 and set(t['monomial'])<=defined for t in w['value']),name+' canonical constructor')
  require(env[w['name']]==ring.positive_poly(w['value'],env),name+' constructor value')
  expected=collections.defaultdict(int)
  expected[(w['name'],)]+=1
  for t in w['value']:expected[tuple(t['monomial'])]-=t['coefficient']
  actual={tuple(t['monomial']):t['coefficient'] for t in old['quadratic_residuals'][j]}
  require({m:v for m,v in expected.items() if v}==actual,name+' defining row')
  defined.add(w['name'])
 remaining=old['quadratic_residuals'][len(old['wires']):]
 guard=remaining[:1] if name=='bundle' else []
 require(b['guards']==guard,name+' preserved side condition')
 for res in remaining[len(guard):]:
  pos,neg=ring.split_poly(res,env)
  require(pos==neg,name+' projected original row is an exact identity')
 require((rv[b['p']],rv[b['q']],rv[b['v']])==(env['p'],env['q'],env['v']),name+' bound labels')
 projected.append({'name':name,'constructor_coordinates_removed':len(old['wires']),
                   'side_conditions_retained':len(guard),'all_projected_rows':'exact identities'})

# The reconstructed local polynomial has beta rows outside the disjunction,
# and one rule-specific guard/update sum of squares inside each alternative.
one=ring.con(1);M=ring.add(rowvars['M0'],one)
beta=[]
for at,ix in [('i',rowvars['i']),('next',ring.add(rowvars['i'],one))]:
 modulus=ring.add(ring.mul(ring.add(ix,one),rowvars['y']),one)
 r,q=(rowvars['x.'+at+'.'+j] for j in ['remainder','quotient'])
 beta.append((rowvars['x'],ring.add(ring.mul(q,modulus),r)))
alternatives=[]
for old in horn['branches']:
 b=branches[old['name']];env={key:rv[value] for key,value in b['bindings'].items()}
 update=(ring.mul(rowvars['x.next.remainder'],ring.add(ring.mul(env['v'],M),one)),
         ring.product([rowvars['x.i.remainder'],ring.add(ring.mul(env['p'],M),one),ring.add(ring.mul(env['q'],M),one)]))
 alternatives.append(ring.sos([ring.split_poly(g,env) for g in b['guards']]+[update]))
expected=ring.iadd(ring.iproduct(alternatives),ring.sos(beta))
require(tuple(rv[i] for i in row['output'])==expected,'complete projected local polynomial')

# The global arithmetic interfaces are checked against the literal call ledger.
gv=ring.load(circuit['nodes'],[ring.var(('global',i)) for i in range(len(circuit['variable_names']))])
G=lambda i:gv[i]
global_names={name:ring.var(('global',i)) for i,name in enumerate(circuit['variable_names'])}
N,x,y,M0=(global_names[j] for j in ['N','x','y','M0']);U=G(source['U'])
require(circuit['variable_names'][:4]==['N','x','y','M0'],'four outer parameters')
require([G(i) for i in source['coordinate_bounds']]==[N]*4+[y,U,y,U],'heterogeneous coordinate bounds')
upper_expected=[N,x,y,M0,N]+[N]*4+[y,U,y,U]
require([G(i) for i in source['upper_environment']]==upper_expected,'upper evaluation environment')
encoded_expected=[N,x,y,M0,G(source['index'])]+[G(i) for i in source['encoded_coordinates']]
require([G(i) for i in source['encoded_environment']]==encoded_expected,'encoded evaluation environment')
ue=ring.load(row['nodes'],upper_expected);ee=ring.load(row['nodes'],encoded_expected)
require((G(source['upper_e']),G(source['upper_f']))==tuple(ue[i] for i in row['output']),'upper natural polynomials')
require((G(source['encoded_e']),G(source['encoded_f']))==tuple(ee[i] for i in row['output']),'encoded natural polynomials')
majorant_values=ring.load(row['nodes'],[N,x,y,M0,N]+[N]*4+[ring.con(0)]*4)
H=ring.sum(majorant_values[branches[b['name']][label]] for b in horn['branches'] for label in ['p','q','v'])
require(G(source['label_majorant'])==H,'literal monotone label majorant')
height=ring.add(ring.product([ring.con(2),H,N]),one)
require(G(source['height_exponent'])==height,'padded height exponent')
ledger=circuit['call_ledger']
def call_result(kind,args):
 matches=[c for c in ledger if c['kind']==kind and [G(i) for i in c['arguments']]==args]
 require(len(matches)==1,kind+' unique literal call')
 result=matches[0]['result']
 return G(result) if isinstance(result,int) else tuple(G(i) for i in result)
equalities={(G(a),G(b),label) for a,b,label in circuit['equalities']}
power=call_result('pow',[ring.con(2),height])
require(G(source['height_power'])==power and (M0,power,'padded binary height') in equalities,'height binding')
L=ring.sum([G(source['upper_e']),G(source['upper_f']),N,U,y,one])
require(G(source['scale_argument'])==L,'scale exceeds all three coordinate bounds plus one')
T=call_result('fact',[L])
require(G(source['T'])==T,'factorial scale')
Q=ring.add(call_result('pow',[ring.add(ring.mul(ring.add(N,one),T),one),N]),ring.con(2))
require(G(source['Q'])==Q,'CRT Q')
tn=call_result('pow',[T,N]);nf=call_result('fact',[N])
choose=call_result('choose',[ring.add(Q,N),N])
modulus=G(source['modulus'])
require((ring.mul(T,Q),ring.add(modulus,one),'CRT positive modulus predecessor') in equalities,'CRT positive divisor')
_,B=call_result('divmod',[ring.product([tn,nf,choose]),modulus])
require(G(source['B'])==B,'CRT product')
require(G(source['N_factorial'])==nf,'CRT factorial remains bound')
for j,item in enumerate(source['coordinate_certificates']):
 bound=([N]*4+[y,U,y,U])[j]
 require(G(item['bound'])==bound,'coordinate role')
 binomial=call_result('choose',[G(item['encoded']),ring.add(bound,one)])
 require(G(item['choose'])==binomial,'coordinate binomial')
 require((binomial,ring.mul(B,G(item['quotient'])),'cancelled-factorial coordinate certificate') in equalities,'coordinate cancelled-factorial equation')
index_left=ring.add(ring.mul(ring.add(G(source['index']),one),T),one)
require((index_left,ring.mul(B,G(source['index_quotient'])),'encoded row index') in equalities,'index certificate')
for i,want in [(ring.con(0),ring.add(M0,ring.con(2))),(N,one)]:
 modulus=ring.add(ring.mul(ring.add(i,one),y),one)
 _,r=call_result('divmod',[x,modulus])
 require((r,want,'beta endpoint') in equalities,'exact beta endpoint')
q0=next(i for i,s in enumerate(circuit['variable_names']) if s.startswith('row evaluation.q0.'))
q1=next(i for i,s in enumerate(circuit['variable_names']) if s.startswith('row evaluation.q1.'))
left=ring.add(G(source['encoded_e']),ring.mul(B,ring.var(('global',q0))))
right=ring.add(G(source['encoded_f']),ring.mul(B,ring.var(('global',q1))))
require((left,right,'encoded row evaluation congruence') in equalities,'row congruence')
report={'status':'PASS','local_witness_columns':8,'projected_branches':projected,
        'identity_method':'Compositional exact integer-polynomial identities in a canonical expression DAG; no sampling',
        'source_interfaces_checked':['beta endpoints','padded label majorant','mixed N/y/U bounds','CRT product','factorial cancellation scale','all coordinate certificates','row congruence'],
        'counts':{'power_calls':sum(c['kind']=='pow' for c in ledger),'binomial_calls':sum(c['kind']=='choose' for c in ledger),'semantic_inputs':len(circuit['variable_names'])},
        'scope':'Checks projection and literal composition interfaces. Unbounded padding, CRT, Horn soundness and inherited arithmetic primitive theorems are proved in the accompanying paper.',
        'sha256':{name:hashlib.sha256((R/name).read_bytes()).hexdigest() for name in ['horn_shared_source.json','row_source.json','circuit.json']}}
(R/'PROJECTION_CHECK.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
