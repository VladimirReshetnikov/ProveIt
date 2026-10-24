#!/usr/bin/env python3
"""Independent local-algebra, complete-prefix and exact-degree audit; no builder import."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from math import gcd,isqrt
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
REPO=RESEARCH.parents[1]
OPS={'add','sub','mul'}
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('reviewed_norm_checker',RESEARCH/'candidates/position-zero-norm-sharing/check.py')
frozen=importlib.util.module_from_spec(spec);spec.loader.exec_module(frozen)
need=frozen.need
add,mul=frozen.add,frozen.mul

def h(raw):return sha256(raw).hexdigest()
def atom(s):return{(s,):1}
def const(n):return{():n}if n else{}
def neg(p):return{k:-v for k,v in p.items()}
def sub(p,q):return add(p,q,-1)
def sq(p):return mul(p,p)
def times(n,p):return mul(const(n),p)
def load(p):return json.loads(p.read_text())
def norm(graph,output,cuts):return frozen.normal_form(dict(graph,output=output),cuts)

def topology(g,expected):
 nodes=g['nodes'];cnt=Counter()
 for i,n in enumerate(nodes):
  need(n['kind']in OPS|{'literal','fixed','variable'},'known kind')
  if n['kind']in OPS:
   need(all(type(n[x])is int and 0<=n[x]<i for x in ['left','right']),'strict topology')
   cnt[n['kind']]+=1
 live=set();todo=[g['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i);n=nodes[i]
  if n['kind']in OPS:todo.extend([n['left'],n['right']])
 need(live==set(range(len(nodes))),'all nodes live')
 need(sum(cnt.values())==expected==g['total_operations'],'operation count')
 need(dict(cnt)==g['operation_counts'],'kind counts')
 need(g['domain']=='strictly positive integers'and len(g['variables'])==9,'positive nine domain')
 need(sorted(n['name']for n in nodes if n['kind']=='variable')==sorted(g['variables']),'all nine input leaves')
 return dict(nodes=len(nodes),operations=sum(cnt.values()),operation_counts=dict(cnt),all_nodes_live=True)

def local_check(parent,g,expected):
 receipt=topology(g,expected);mapping={int(i):j for i,j in g['core_clone_map'].items()}
 covered=set()
 for i,j in mapping.items():
  need(0<=i<len(parent['nodes'])and 0<=j<len(g['nodes']),'remap range')
  n=dict(parent['nodes'][i])
  if n['kind']in OPS:
   need(n['left']in mapping and n['right']in mapping,'closed retained prefix')
   n.update(left=mapping[n['left']],right=mapping[n['right']])
  need(n==g['nodes'][j],'complete retained register identity');covered.add(j)
 for field in ['variables','domain','coefficient_recipes','fixed_binding','coherent_tuple','source_snapshot',
               'base_scale_exponent','threshold_scale_exponent','source_degree','threshold_degree','A_degree','W']:
  need(g[field]==parent[field],'whole inherited binding '+field)
 need({n['name']for n in g['nodes']if n['kind']=='fixed'}=={n['name']for n in parent['nodes']if n['kind']=='fixed'},'all fixed leaves retained and live')
 names=g['named_nodes'];idx=lambda k:names[k]
 def old(k):return mapping[parent['named_nodes'][k]]
 for child,oldname in [('A','A'),('C','C'),('J','J'),('Delta','Am1'),('first','a0'),('Omega','Omega'),('E0','E0'),('B1','B1')]:
  need(idx(child)==old(oldname),'semantic source cut '+child)
 def variable(name):
  i=next(i for i,n in enumerate(parent['nodes'])if n['kind']=='variable'and n['name']==name)
  return mapping[i]
 def prove(label,cuts,p):
  out=g['output']if label=='output'else idx(label)
  got,seen=norm(g,out,{i:name for name,i in cuts.items()})
  need(got==p,'exact local recipe '+label);covered.update(seen)
  return len(got)
 A,C,J,D,E,q,F,L,G,Z,H,W,I,V,Om,T,Ac,B=[atom(x)for x in ['A','C','J','Delta','e','q','F','L','G','Z','H','W','I','V','Om','T','a','B']]
 checks={}
 checks['first']=prove('first',{'P':old('P'),'K':old('K')},add(const(1),mul(sub(sq(atom('P')),const(1)),sq(atom('K')))))
 checks['Delta']=prove('Delta',{'A':idx('A')},sub(sq(A),const(1)))
 checks['e']=prove('eFull',{'C':idx('C'),'J':idx('J'),'i':variable('i')},mul(mul(J,atom('i')),sq(C)))
 checks['F']=prove('F',{'Delta':idx('Delta'),'q':idx('first'),'e':idx('eFull')},add(const(1),mul(mul(D,q),sq(E))))
 checks['Lambda']=prove('Lambda',{'A':idx('A'),'C':idx('C')},add(const(1),mul(A,sub(C,const(1)))))
 checks['G']=prove('G',{'A':idx('A'),'F':idx('F'),'L':idx('Lambda')},add(A,mul(F,L)))
 checks['Z']=prove('Z',{'B':idx('B1'),'C':idx('C'),'j':variable('j')},add(B,mul(sub(atom('j'),const(1)),C)))
 checks['H']=prove('H',{'C':idx('C'),'F':idx('F'),'Z':idx('Z')},add(C,mul(F,Z)))
 checks['GH']=prove('GH',{'G':idx('G'),'H':idx('H')},mul(G,H))
 checks['I']=prove('I',{'G':idx('G'),'H':idx('H')},add(const(1),mul(sub(sq(G),const(1)),sq(H))))
 checks['a']=prove('Ac',{'q':idx('first'),'F':idx('F')},mul(q,F))
 checks['V']=prove('Vc',{'A':idx('A'),'q':idx('first'),'e':idx('eFull')},mul(mul(A,q),E))
 checks['Theta']=prove('Theta',{'E':idx('E0'),'Om':idx('Omega'),'V':idx('Vc'),'W':idx('GH')},sub(atom('E'),mul(Om,add(V,W))))
 expected_norm=sub(sq(sub(sq(T),mul(sq(Om),add(Ac,I)))),times(4,mul(sq(sq(Om)),mul(Ac,I))))
 checks['output']=prove('output',{'T':idx('Theta'),'Om':idx('Omega'),'a':idx('Ac'),'I':idx('I')},expected_norm)
 need(covered==set(range(len(g['nodes']))),'every new node justified by retained source or a proved local formula')
 receipt.update(retained_nodes=len(mapping),local_formula_term_counts=checks,all_nodes_algebraically_covered=True)
 return receipt

def identities():
 # Complete polynomial identities, with no use of source values.
 E,O,V,W,a,b=[atom(s)for s in ['E','O','V','W','a','b']]
 dc,di=sub(sq(V),a),sub(sq(W),b)
 theta=sub(E,mul(O,add(V,W)))
 left=sub(sq(sub(sq(theta),mul(sq(O),add(a,b)))),times(4,mul(sq(sq(O)),mul(a,b))))
 small=add(sub(sq(E),times(2,mul(mul(E,O),add(V,W)))),mul(sq(O),add(dc,di)))
 right=add(add(sq(small),times(4,mul(mul(mul(sq(O),V),W),small))),times(4,mul(sq(sq(O)),add(mul(dc,sq(W)),mul(a,di)))))
 need(left==right,'complete centered norm identity')
 A,q,e=atom('A'),atom('q'),atom('e')
 f=add(const(1),mul(mul(sub(sq(A),const(1)),q),sq(e)))
 aa=mul(q,f);vv=mul(mul(A,q),e)
 need(sub(sq(vv),aa)==mul(q,sub(mul(q,sq(e)),const(1))),'exact first majorant defect')
 G,H=atom('G'),atom('H');ii=add(const(1),mul(sub(sq(G),const(1)),sq(H)))
 need(sub(sq(mul(G,H)),ii)==sub(sq(H),const(1)),'exact auxiliary majorant defect')
 return dict(complete_centered_identity_terms=len(left),first_defect_terms=len(sub(sq(vv),aa)),second_defect_terms=2)

def degree_witness(g,fixed):
 deg=[]
 for n in g['nodes']:
  k=n['kind']
  deg.append(1 if k=='variable'else 0 if k not in OPS else
             deg[n['left']]+deg[n['right']]if k=='mul'else max(deg[n['left']],deg[n['right']]))
 need(deg[g['output']]==g['degree_upper_bound']==g['syntactic_degree'],'raw degree bound')
 d,r,w=g['A_degree'],g['source_degree'],g['W'];need(d==r+4*g['threshold_degree']+2,'source degree relation')
 expected={'A':d,'C':1,'J':d,'Delta':2*d,'eFull':d+3,'first':6*d+2*r+2,
           'F':10*d+2*r+8,'Lambda':d+1,'G':11*d+2*r+9,'Z':r,'H':10*d+3*r+8,
           'GH':21*d+5*r+17,'I':42*d+10*r+34,'Ac':16*d+4*r+10,'Vc':8*d+2*r+5,
           'Omega':5*d+2*w+3,'E0':d+4,'B1':r,'de':7*d+2*r+5,'Theta':26*d+5*r+2*w+20}
 need(all(deg[g['named_nodes'][name]]==v for name,v in expected.items()),'every core degree bound')
 four=[60*d+12*r+8*w+44,69*d+13*r+8*w+50,76*d+14*r+8*w+56,56*d+10*r+8*w+38]
 qd,ed,od,vd,wd,ad,e0d=[deg[g['named_nodes'][k]]for k in ['first','eFull','Omega','Vc','GH','Ac','E0']]
 dcd=max(2*qd+2*ed,qd);did=max(2*deg[g['named_nodes']['H']],0)
 sd=max(2*e0d,e0d+od+max(vd,wd),2*od+max(dcd,did))
 need(four==[2*sd,2*od+vd+wd+sd,4*od+dcd+2*wd,4*od+ad+did],'computed degree bounds for complete four-term identity')
 need(four[2]==g['exact_degree']==g['expected_exact_degree']and all(four[j]<four[2]for j in (0,1,3)),'unique top centered term')
 witnesses=[]
 for p in [65537,1000000007,2147483647]:
  coeff=[]
  for i,n in enumerate(g['nodes']):
   k=n['kind']
   if k=='variable':v=1
   elif k=='fixed':v=fixed[n['name']]%p
   elif k=='literal':v=n['value']%p
   else:
    l,rn=n['left'],n['right']
    v=coeff[l]*coeff[rn]if k=='mul'else (coeff[l]if deg[l]==deg[i]else 0)+(1 if k=='add'else -1)*(coeff[rn]if deg[rn]==deg[i]else 0)
   coeff.append(v%p)
  lc={k:coeff[g['named_nodes'][k]]for k in ['Omega','first','eFull','GH']}
  top=4*lc['Omega']**4*lc['first']**2*lc['eFull']**2*lc['GH']**2%p
  need(top!=0,'exact nonzero highest homogeneous diagonal witness')
  witnesses.append(dict(prime=p,variable_diagonal='all nine coordinates equal T',core_leading_values=lc,output_top_value=top))
 return dict(exact_degree=g['exact_degree'],raw_degree_bound=deg[g['output']],centered_term_degree_bounds=four,
             dominant_term='4*Omega^4*(V^2-a)*(G*H)^2',nonzero_diagonal_leading_witnesses=witnesses)

def pell(A,k):
 x,y=1,0
 for _ in range(k):x,y=A*x+(A*A-1)*y,x+A*y
 return x,y

def finite_controls():
 count=0
 for A in range(3,9):
  for q in range(1,11):
   f,ordinate=pell(A,q)
   need(f>2*ordinate,'Pell separation control')
   for t in range(4*q+1):
    _,pt=pell(A,t);rr=t%(2*q);r=min(rr,2*q-rr)
    pr=pell(A,r)[1]
    need((pt-pr)%f==0 or(pt+pr)%f==0,'signed residue folding control')
    need(t%(2*q)in {r% (2*q),(-r)%(2*q)},'folded index control');count+=1
 square_cases=0;majorants=0
 for A in range(3,9):
  for q in range(1,21):
   for e in range(1,8):
    F=1+(A*A-1)*q*e*e
    need(gcd(q,F)==1,'saturation coprimality control')
    square=lambda x:isqrt(x)**2==x
    need(square(q*F)==(square(q)and square(F)),'individual square extraction control');square_cases+=1
  for C in range(1,5):
   for first in range(1,6):
    for i in range(1,3):
     e=i*A*C*C;F=1+(A*A-1)*first*e*e;G=A+F*(1+A*(C-1));H=C+F*2
     I=1+(G*G-1)*H*H;V=A*first*e;aa=first*F
     need(V*V-aa==first*(first*e*e-1)>0,'strict first majorant control')
     need((G*H)**2-I==H*H-1>0 and I>aa,'strict auxiliary majorant and unequal roots control');majorants+=1
 return dict(folded_residue_cases=count,coprime_square_cases=square_cases,strict_majorant_cases=majorants,
             scope='Finite diagnostics only; the unbounded period and source witness maps are proved in PROOF.md.')

def run():
 build=load(HERE/'BUILD.json')
 need(h((HERE/'build.py').read_bytes())==build['generator_sha256'],'bound generator source')
 need(h(Path(__file__).read_bytes())==build['independent_checker_sha256'],'bound independent checker source')
 need(h((HERE/'PROOF.md').read_bytes())==build['proof_sha256'],'bound ordinary proof')
 for name,pin in load(HERE/'MANIFEST.json').items():need(h((HERE/name).read_bytes())==pin,'entire packet seal '+name)
 for name,pin in build['generated_files'].items():need(h((HERE/name).read_bytes())==pin,'generated file pin '+name)
 pins=load(HERE/'SOURCE_PINS.json')
 for rel,pin in pins['retained_files'].items():need(h((RESEARCH/rel).read_bytes())==pin,'retained proof/helper pin '+rel)
 need(h((REPO/pins['archive']).read_bytes())==pins['archive_sha256'],'whole immutable source archive')
 generic=identities();cases=[]
 with frozen.load_archive()as z:
  for name,expected_ops in [('boundary_simple',414),('compact_simple',422)]:
   p=pins['parents'][name];raw=(RESEARCH/p['path']).read_bytes();need(h(raw)==p['sha256'],'whole parent graph pin')
   parent=json.loads(raw);g=load(HERE/(name+'.json'))
   need(g['parent_sha256']==p['sha256'],'embedded source pin')
   literal=local_check(parent,g,expected_ops)
   fixed,binding=frozen.fixed_values(z,'boundary'if name.startswith('boundary')else'compact',parent)
   degree=degree_witness(g,fixed);mutations=[]
   def reject(bad,label):
    try:local_check(parent,bad,expected_ops)
    except(ValueError,KeyError,IndexError,StopIteration):mutations.append(label);return
    raise ValueError('corruption accepted '+label)
   bad=deepcopy(g);bad['nodes'][bad['output']]['kind']='add';reject(bad,'wrong final norm sign')
   bad=deepcopy(g);i=next(i for i,n in enumerate(bad['nodes'])if n['kind']=='fixed');bad['nodes'][i]['name']='wrong_fixed';reject(bad,'altered complete fixed binding')
   bad=deepcopy(g);bad['nodes'][bad['named_nodes']['de']]['left']=bad['named_nodes']['A'];reject(bad,'wrong saturation factor')
   bad=deepcopy(g);bad['core_clone_map'][str(parent['named_nodes']['a0'])]=bad['named_nodes']['Delta'];reject(bad,'wrong retained source cut')
   cases.append(dict(name=name,whole_tuple=g['coherent_tuple'],literal=literal,degree=degree,
                     fixed_binding=binding,rejected_mutations=mutations))
 return dict(status='PASS',optimized_python=bool(sys.flags.optimize),generic_identities=generic,
             cases=cases,finite_controls=finite_controls(),
             scope='New ordinary two-way Pell reduction, complete literal prefix/local algebra and actual-coefficient degree evidence. Native/refutation source bridge inherited; no Lean or internal-ZFC claim.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
 result=run();raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if args.output:args.output.write_text(raw)
 print(raw,end='')
if __name__=='__main__':main()
