#!/usr/bin/env python3
"""Independent exact shared-Fminus1 reflection, full fixed values, norm and degree audit."""
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
PARENT=HERE.parent/'nine-folded-reflected-parameter'
OPS={'add','sub','mul'}
spec=importlib.util.spec_from_file_location('accepted_reflected_checker',PARENT/'check.py')
accepted=importlib.util.module_from_spec(spec);spec.loader.exec_module(accepted)
frozen=accepted.frozen
algebra=accepted.accepted
need=accepted.need

def load(p):return json.loads(p.read_bytes())
def digest(raw):return sha256(raw).hexdigest()

def sealed(path):
 m=path/'MANIFEST.json';pins=load(m);pins=pins.get('files',pins)
 need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p!=m}==set(pins),'closed whole packet '+str(path))
 for n,h in pins.items():need(digest((path/n).read_bytes())==h,'sealed whole member '+n)

def local_check(parent,g,expected):
 receipt=algebra.topology(g,expected);old=parent['nodes'];nodes=g['nodes'];mapping={int(i):j for i,j in g['parent_clone_map'].items()}
 labels=parent['named_nodes'];A,F,C,lam,G=[labels[n]for n in['A','F','C','Lambda','G']]
 one=next(i for i,n in enumerate(old)if n==dict(kind='literal',value=1))
 need(old[G]['kind']=='sub'and old[G]['right']==A,'exact previous reflectedG subtraction')
 gf=old[G]['left'];need(old[gf]==dict(kind='mul',left=F,right=lam),'oldF Lambda product')
 need(old[lam]['kind']=='add'and old[lam]['right']==one,'old Lambda plus1')
 ac=old[lam]['left'];need(old[ac]==dict(kind='add',left=A,right=C),'old privateAplusC')
 need(old[F]['kind']=='add'and old[F]['left']==one,'literal originalF equals1 plus existing product')
 fm1=old[F]['right'];need(old[fm1]['kind']=='mul','exact existing completeFminus1 product')
 deleted={ac,lam,gf}
 need(g['deleted_parent_nodes']==sorted(deleted)and g['changed_parent_nodes']==[G],'only three private deletions andG change')
 need(set(mapping)==set(range(len(old)))-deleted,'complete retained parent inventory')
 for i,j in mapping.items():
  need(type(j)is int and 0<=j<len(nodes),'mapped node range')
  if i==G:continue
  n=dict(old[i])
  if n['kind']in OPS:n.update(left=mapping[n['left']],right=mapping[n['right']])
  need(n==nodes[j],'all literal retained operators/operands and fixed values')
 need(len(set(mapping.values()))==len(mapping),'injective retained-node mapping')
 cg=mapping[G];node=nodes[cg];need(node['kind']=='add'and node['right']==mapping[F],'newG adds exactF')
 af=node['left'];need(nodes[af]==dict(kind='mul',left=mapping[A],right=mapping[fm1]),'newG shares exact existingFminus1')
 need(g['inserted_child_nodes']==[af]and set(mapping.values())|{af}==set(range(len(nodes))),'complete one-node insertion inventory')
 need(set(g['named_nodes'])==(set(labels)-{'Lambda'})|{'Fminus1'},'no unusedLambda introduced as hidden operation')
 for label,index in labels.items():
  if label!='Lambda':need(g['named_nodes'][label]==mapping[index],'every retained named cut '+label)
 need(g['named_nodes']['Fminus1']==mapping[fm1],'new named sharedFminus1 is exact retained product')
 for field in ['variables','domain','coefficient_recipes','fixed_binding','coherent_tuple','source_snapshot','base_scale_exponent',
               'threshold_scale_exponent','source_degree','threshold_degree','A_degree','W']:
  need(g[field]==parent[field],'complete unchanged source binding '+field)
 need(g['output']==mapping[parent['output']],'same final output recipe')
 A,F=[algebra.atom(v)for v in['A','F']]
 got,seen=frozen.normal_form(dict(g,output=cg),{mapping[labels['A']]:'A',mapping[fm1]:'Fm1',mapping[labels['F']]:'F'})
 expectedG=algebra.add(algebra.mul(A,algebra.atom('Fm1')),F)
 need(got==expectedG,'all coefficients of actual sharedG expression')
 # Distinct universal identity: the storedFm1 really isF-1 (literalF gate),
 # and substitution gives exactly the proposed three-operation parameter.
 minimal=algebra.add(algebra.mul(A,algebra.sub(F,algebra.const(1))),F)
 unshared=algebra.sub(algebra.mul(F,algebra.add(A,algebra.const(1))),A)
 need(minimal==unshared,'universal completeG sharing identity')
 T,O,a,I=[algebra.atom(v)for v in['T','O','a','I']]
 expectedN=algebra.sub(algebra.sq(algebra.add(algebra.sq(T),algebra.mul(algebra.sq(O),algebra.sub(a,I)))),
   algebra.times(4,algebra.mul(algebra.mul(algebra.sq(O),a),algebra.sq(T))))
 n=g['named_nodes'];got,_=frozen.normal_form(g,{n['Theta']:'T',n['Omega']:'O',n['Ac']:'a',n['I']:'I'})
 need(got==expectedN,'all coefficients of complete two-root norm')
 for i in deleted:
  consumers={j for j,node in enumerate(old)if node['kind']in OPS and i in[node['left'],node['right']]}
  need(consumers<=(deleted|{G}),'complete privacy of deleted parameter nodes')
 receipt.update(all_parent_nodes_accounted=True,private_deleted_nodes=sorted(deleted),changed_parent_G=G,
   actual_shared_G_terms=len(expectedG),exact_stored_Fminus1=True,universal_sharing_identity=True,all_new_nodes_algebraically_covered=True)
 return receipt


def degree_witness(g,fixed):
 deg=[]
 for n in g['nodes']:
  k=n['kind']
  deg.append(1 if k=='variable'else 0 if k not in OPS else
             deg[n['left']]+deg[n['right']]if k=='mul'else max(deg[n['left']],deg[n['right']]))
 need(deg[g['output']]==g['degree_upper_bound']==g['syntactic_degree'],'raw degree bound')
 d,r,w=g['A_degree'],g['source_degree'],g['W'];need(d==r+4*g['threshold_degree']+2,'source degree relation')
 expected={'A':d,'C':1,'J':d,'eFull':3,'first':6*d+2*r+2,
           'F':8*d+2*r+8,'Fminus1':8*d+2*r+8,'G':9*d+2*r+8,'Z':r,'H':8*d+3*r+8,
           'GH':17*d+5*r+16,'I':34*d+10*r+32,'Ac':14*d+4*r+10,'Vc':7*d+2*r+5,
           'Omega':5*d+2*w+3,'E0':d+1,'B1':r,'de':6*d+2*r+5,'Theta':22*d+5*r+2*w+19}
 need(all(deg[g['named_nodes'][name]]==v for name,v in expected.items()),'every core degree bound')
 four=[52*d+12*r+8*w+44,60*d+13*r+8*w+49,66*d+14*r+8*w+54,50*d+10*r+8*w+38]
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
 reflection=folding=positive=periods=0
 for A in range(3,10):
  for t in range(1,19):
   need(pell(-A,t)[1]==(-1)**(t-1)*pell(A,t)[1],'exact signed parameter identity');reflection+=1
  for q in range(1,9):
   f,ordinate=pell(A,q)
   for t in range(1,4*q+2):
    residue=pell(-A,t)[1]%f;rr=t%(2*q);r=min(rr,2*q-rr);pr=pell(A,r)[1]
    need(residue in{pr%f,(-pr)%f},'signed reflection preserves folded index');folding+=1
 for A in range(3,8):
  for C in range(1,7):
   for a0 in range(2,7):
    e=C*C;F=1+(A*A-1)*a0*e*e;G=A*(F-1)+F;H=C+F*(3+C)
    need(G>F>a0 and G%F==(-A)%F and G%C==1%C,'positive parameter and both exact residue conditions')
    need((G*H)**2-(1+(G*G-1)*H*H)==H*H-1>0,'strict majorant defect');positive+=1
 # Actual bounded matrix periods, with C=psi_A(B1), B1 odd. This is
 # a finite control only; existence for arbitrary modulus is the group proof.
 for A in[3,4]:
  B1=3;C=pell(A,B1)[1];F=2*C+1;G=A*(F-1)+F
  x0,y0=1,0
  for T in range(1,20*F*F+1):
   x0,y0=(G*x0+(G*G-1)*y0)%F,(x0+G*y0)%F
   if(x0,y0)==(1,0):break
  else:raise ValueError('bounded control period absent')
  t=B1+T*C*F*(B1+1)
  # Exact modular exponentiation avoids constructing enormous Pell values.
  modulus=F*C;delta=(G*G-1)%modulus
  def product(u,v):return((u[0]*v[0]+delta*u[1]*v[1])%modulus,(u[0]*v[1]+u[1]*v[0])%modulus)
  result=(1,0);base=(G%modulus,1);exponent=t
  while exponent:
   if exponent%2:result=product(result,base)
   base=product(base,base);exponent//=2
  h=result[1]
  need(h%F==C%F and h%C==B1%C and(h-C)%F==0 and((h-C)//F)%C==B1%C,
       'exact combined-modulus positive-j period residues')
  need(t>C+F*B1,'strict index bound ensuring psiG(t)>C+F*B1');periods+=1
 return dict(reflection_cases=reflection,signed_fold_cases=folding,positive_parameter_cases=positive,
   actual_period_cases=periods,scope='Finite controls supplement the unbounded ordinary proof.')

def main():
 if(HERE/'MANIFEST.json').exists():sealed(HERE)
 sealed(PARENT)
 pins=load(HERE/'SOURCE_PINS.json')
 for path,h in pins['retained_files'].items():need(digest((BASE/path).read_bytes())==h,'complete pinned dependency '+path)
 need(pins['proof_sha256']==digest((HERE/'PROOF.md').read_bytes())and pins['generator_sha256']==digest((HERE/'build.py').read_bytes()),'proof and generator pins')
 generic=algebra.identities();cases=[]
 with frozen.load_archive()as z:
  for name,count in[('boundary_simple',406),('compact_simple',414)]:
   parent=load(PARENT/(name+'.json'));g=load(HERE/(name+'.json'))
   need(g['parent_sha256']==digest((PARENT/(name+'.json')).read_bytes()),'whole immediate parent')
   literal=local_check(parent,g,count);fixed,binding=frozen.fixed_values(z,'boundary'if name.startswith('boundary')else'compact',parent)
   degree=degree_witness(g,fixed);rejected=[]
   for label,change in[
    ('wrong_reflection_sign',lambda b:b['nodes'][b['named_nodes']['G']].__setitem__('kind','sub')),
    ('wrong_shared_Fminus1',lambda b:b['named_nodes'].__setitem__('Fminus1',b['named_nodes']['F'])),
    ('norm_sign',lambda b:b['nodes'][b['output']].__setitem__('kind','add')),
    ('source_port',lambda b:next(n for n in b['nodes']if n['kind']=='fixed').__setitem__('name','wrong')),
    ('wrong_domain',lambda b:b.__setitem__('domain','natural integers'))]:
    bad=deepcopy(g);change(bad)
    try:local_check(parent,bad,count)
    except(ValueError,KeyError,IndexError):rejected.append(label)
    else:raise ValueError('mutation accepted '+label)
   cases.append(dict(name=name,literal=literal,degree=degree,fixed_binding=binding,rejected_mutations=rejected))
 result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),cases=cases,complete_inherited_norm_identities=generic,
   finite_controls=finite_controls(),proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
   scope='Complete actual circuits, all fixed integers, unique highest-degree term and exact nonzero leading witnesses. Ordinary signed-parameter existential theorem is PROOF.md; no new calibration, Lean or internal-ZFC endpoint.')
 target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
