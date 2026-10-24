#!/usr/bin/env python3
"""Independent complete guard-substitution, norm, degree and coefficient audit."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from math import gcd,isqrt
from pathlib import Path
import random
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'candidates/constructive-integer14-quadratic-shared'
PARENT_SHA='307015e68eb300713d06076b0c3c78f1017fe74dbe79f6b89385292637d1ec41'
OPS={'add','sub','mul'}
def need(x,s):
 if not x:raise ValueError(s)
def sha(x):return sha256(x).hexdigest()
def load(p):return json.loads(p.read_bytes())
def ancestors(g,out):
 seen=set();todo=[out]
 while todo:
  i=todo.pop()
  if i in seen:continue
  seen.add(i);r=g['nodes'][i]
  if r[0]in OPS:todo.extend(r[1:])
 return seen

def verify_map(parent,child,cert):
 old,new=parent['nodes'],child['nodes'];records=cert['all_parent_nodes'];nm=parent['named_registers']
 need([r['parent']for r in records]==list(range(len(old))),'everyparentnodeaccounted')
 alias=cert['aliased_guard_argument_parent'];removed=cert['deleted_v_square_parent'];G=cert['replacement_parent']
 need(alias==nm['Gv']and G==nm['G'],'literalguardcut')
 v=next(i for i,r in enumerate(old)if r==['variable','v'])
 need(old[removed]==['mul',v,v]and old[alias]==['mul',G,removed],'oldv²Gdefinition')
 need([j for j,r in enumerate(old)if r[0]in OPS and removed in r[1:]]==[alias],'v²soleuse')
 mapping={r['parent']:r['child']for r in records if r['status']!='removed_private'}
 need(len(new)==144 and len(set(mapping.values()))==144,'completechildcoverage')
 for rec in records:
  i=rec['parent'];r=old[i]
  if i==removed:
   need(rec==dict(parent=i,status='removed_private',old_row=r),'exactremoveddefinition');continue
  if i==alias:
   need(rec==dict(parent=i,status='guard_alias',child=mapping[G],replacement_parent=G,old_row=r),'explicitaliasrecord');continue
  need(rec['status']=='retained','noadditionaldeletedoraliasnode')
  want=[r[0],mapping[r[1]],mapping[r[2]]]if r[0]in OPS else r
  need(new[mapping[i]]==want,'everyretainedinstructionincludingcompleteoperands')
 need(mapping[alias]==mapping[G],'GvissubstitutedbyG')
 need(child['named_registers']=={k:mapping[i]for k,i in nm.items()if k!='Gv'},'onlyoldGvlabelretired')
 need(child['output']==mapping[parent['output']],'completeoutputmap')
 norm=ancestors(parent,nm['N']);need(alias not in norm and removed not in norm,'entirenormindependentofguardargument')
 private={i for i,r in enumerate(old)if r[0]=='variable'and r[1]in {'t','p1','p2','p3'}}
 need(not(norm&private),'fourprivateguardvariablesabsentfromentirenorm')
 need(ancestors(child,child['named_registers']['N'])=={mapping[i]for i in norm},'exactfullnormancestorcorrespondence')
 return mapping,removed,alias

def evaluate(g,inputs,p=None):
 vals=[]
 for r in g['nodes']:
  if r[0]=='integer':v=r[1]
  elif r[0]in {'variable','coefficient'}:v=inputs[r[1]]
  else:
   a,b=vals[r[1]],vals[r[2]];v=a+b if r[0]=='add'else a-b if r[0]=='sub'else a*b
  vals.append(v if p is None else v%p)
 return vals

def line_degree(xs,p):
 d=-1;k=0
 while xs:
  if xs[0]:d=k
  xs=[(b-a)%p for a,b in zip(xs,xs[1:])];k+=1
 return d

def main():
 raw=(HERE/'source/parent-equation.json').read_bytes();need(sha(raw)==PARENT_SHA,'complete119parentpin')
 need(raw==(PARENT/'equation.json').read_bytes(),'copiedparentbytes')
 pins=load(HERE/'SOURCE_PINS.json');need(pins['parent_equation_sha256']==PARENT_SHA,'provenanceparent')
 need(sha((PARENT/'MANIFEST.json').read_bytes())==pins['parent_manifest_sha256'],'frozenparentmanifest')
 parent=json.loads(raw);g=load(HERE/'equation.json');cert=load(HERE/'NODE_REMAP.json')
 mapping,removed,alias=verify_map(parent,g,cert);nm=g['named_registers'];nodes=g['nodes'];degrees=[]
 need(g['variables']==parent['variables']and g['variable_count']==14 and
      g['domain']==parent['domain']=='unrestricted integers','samefourteenunrestrictedcoordinates')
 for i,r in enumerate(nodes):
  need(r[0]in OPS|{'integer','variable','coefficient'},'knownpolynomialinstruction')
  if r[0]in OPS:
   need(all(type(j)is int and 0<=j<i for j in r[1:]),'stricttopology')
   degrees.append(degrees[r[1]]+degrees[r[2]]if r[0]=='mul'else max(degrees[r[1]],degrees[r[2]]))
  else:degrees.append(1 if r[0]=='variable'else 0)
 need(ancestors(g,g['output'])==set(range(len(nodes))),'all144nodeslive')
 need([r[1]for r in nodes if r[0]=='variable']==g['variables'],'all14inputslive')
 counts=Counter(r[0]for r in nodes if r[0]in OPS)
 need(dict(counts)==g['operation_counts']=={'mul':66,'add':26,'sub':25}and sum(counts.values())==g['operations']==117,'exact117operations')
 need(degrees[g['output']]==344 and degrees[nm['N']]==288,'rawdegreeboundsseparatefromexactdegrees')
 helper=HERE/'source/independent_norm_oracle.py';spec=importlib.util.spec_from_file_location('signed_guard_independent_oracle',helper)
 oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 oracle.ZERO=(0,)*8
 def variable(i):return oracle.Poly({tuple(int(j==i)for j in range(8)):1})
 def normalize(graph,out,cuts):
  memo={}
  def visit(i):
   if i in cuts:return cuts[i]
   if i not in memo:
    r=graph['nodes'][i]
    if r[0]=='integer':v=oracle.Poly(r[1])
    else:
     need(r[0]in OPS,'alllocalleavescut')
     a,b=visit(r[1]),visit(r[2]);v=a+b if r[0]=='add'else a-b if r[0]=='sub'else a*b
    memo[i]=v
   return memo[i]
  return visit(out)
 x,y,v,t,p1sq,p2sq,tri,n=[variable(i)for i in range(8)]
 pos=1+p1sq+p2sq+tri
 pair=lambda a,b:a*b-(t*t-a-b+1)**2
 Bold=pair(v*v*x,y)-pos;Bnew=pair(x,y)-pos
 oldpos=parent['nodes'][parent['named_registers']['guard']][2]
 oldp2sq=parent['nodes'][parent['nodes'][parent['named_registers']['guard']][1]][2]
 oldp1sq=parent['nodes'][parent['nodes'][parent['nodes'][parent['named_registers']['guard']][1]][1]][2]
 cuts={parent['named_registers']['G']:x,parent['named_registers']['Peta']:y,
       next(i for i,r in enumerate(parent['nodes'])if r==['variable','v']):v,
       next(i for i,r in enumerate(parent['nodes'])if r==['variable','t']):t,oldpos:tri,oldp1sq:p1sq,oldp2sq:p2sq}
 need(normalize(parent,parent['named_registers']['guard'],cuts).t==Bold.t,'completeoldguardformula')
 need(normalize(g,nm['guard'],{mapping[i]:a for i,a in cuts.items()}).t==Bnew.t,'completenewguardformula')
 diff=(1-v*v)*x*(2*t*t-y+2-(1+v*v)*x)
 need((Bnew-Bold).t==diff.t,'completeguarddifferenceidentity')
 full_diff=(n+Bnew**2+n*Bnew**2)-(n+Bold**2+n*Bold**2)
 need(full_diff.t==((Bnew-Bold)*(Bnew+Bold)*(n+1)).t,'completeoutputdifferenceidentity')
 weight=[4,14,1,1,2,2,2,256]
 degree=lambda p:max((sum(a*b for a,b in zip(m,weight))for m in p.t),default=-1)
 need(degrees[nm['G']]==4 and degrees[nm['Peta']]==14,'literalcoreguarddegreebounds')
 need((degree(Bold),degree(Bnew),degree(diff),degree(full_diff))==(28,28,20,304),'strict304differenceboundbelow312')
 # Verify the whole cleared octic using all five formal atoms.
 xx,aa,bb,cc,delta,_=[variable(i)for i in range(6)]
 normcuts={nm['center']:xx,nm['raw_A']:aa,nm['raw_B']:bb,nm['Cn']:cc,nm['delta']:delta}
 expected=delta**4*oracle.norm_oracle(xx,[aa,bb,oracle.Poly({(0,0,0,1,-1,0,0,0):1})])
 need(normalize(g,nm['N'],normcuts).t==expected.t and len(expected.t)==35,'all35clearednormcoefficients')
 # The exact exceptional equality cannot hold modulo3.
 ii,VV=[variable(i)for i in range(2)];df=1+3*ii**2;Q=9*ii**2
 need((Q*VV**2-1-(Q-1)*df).t==(3*ii**2*(3*VV**2-3*df+1)).t,'exactv0equal-rootcontradictionidentity')
 oldnm=parent['named_registers'];one=next(i for i,r in enumerate(parent['nodes'])if r==['integer',1])
 need(parent['nodes'][oldnm['S']]==['mul',oldnm['guard'],oldnm['guard']],'literalguardissquared')
 out=parent['nodes'][parent['output']]
 need(out[0]=='add'and parent['nodes'][out[1]]==['add',oldnm['S'],oldnm['N']]and
      parent['nodes'][out[2]]==['mul',oldnm['S'],oldnm['N']],'literalunitproductfinalizer')
 binding=load(HERE/g['coefficient_binding']);need((HERE/g['coefficient_binding']).read_bytes()==(PARENT/g['coefficient_binding']).read_bytes(),'wholecopiedbinding')
 coeff={};payloads={}
 for name,p in binding['payloads'].items():
  blob=(HERE/'coefficients'/p['file']).read_bytes();need(blob==(PARENT/'coefficients'/p['file']).read_bytes(),'wholecopiedpayload '+name)
  data=gzip.decompress(blob);need(sha(data)==p['raw_sha256']and len(data)==p['raw_bytes'],'fullrawvalue '+name)
  value=int.from_bytes(data,'little');need(value.bit_length()==p['bits'],'actualcoefficientbits')
  coeff[name]=value;payloads[name]=dict(raw_sha256=sha(data),bits=p['bits'])
 need(set(coeff)=={'beta','K0','MC','MF','cone_A','cone_B'}and coeff['beta']==2**1064921-1 and
      coeff['cone_A']==2**1113 and coeff['cone_B']==2**666104,'wholesix-porttuple')
 affected={alias}
 for i,r in enumerate(parent['nodes']):
  if r[0]in OPS and any(j in affected for j in r[1:]):affected.add(i)
 rng=random.Random(117312);controls=0;changed=0
 for prime in [1009,(1<<127)-1]:
  for j in range(50):
   env={v:rng.randrange(-15,16)for v in g['variables']}
   if j%3==0:env['v']=0
   if j%5==0:env['c']=0
   env.update({v:c%prime for v,c in coeff.items()});a,b=evaluate(parent,env,prime),evaluate(g,env,prime)
   need(all(a[i]==b[j]for i,j in mapping.items()if i not in affected),'allunaffectedcoreandnormvalues')
   nn=b[nm['N']];bo=a[oldnm['guard']];bn=b[nm['guard']]
   need((b[g['output']]-a[parent['output']])%prime==((bn-bo)*(bn+bo)*(nn+1))%prime,'wholeoutputdifferencecontrol')
   changed+=int(a[parent['output']]!=b[g['output']]);controls+=1
 need(changed>0,'notfalselyclaimingpointwiseoutputidentity')
 slices=[]
 for prime in [(1<<127)-1,(1<<89)-1]:
  base={v:rng.randrange(1,prime)for v in g['variables']};direction={v:rng.randrange(1,prime)for v in g['variables']};pv=[];nv=[]
  for t0 in range(346):
   env={v:c%prime for v,c in coeff.items()}|{v:(base[v]+t0*direction[v])%prime for v in g['variables']}
   vals=evaluate(g,env,prime);pv.append(vals[g['output']]);nv.append(vals[nm['N']])
  dp,dn=line_degree(pv,prime),line_degree(nv,prime);need((dp,dn)==(312,256),'actualtuple312and256degreeattainment')
  slices.append(dict(prime_bits=prime.bit_length(),output_degree=dp,norm_degree=dn))
 for filename in ['parent-CHECK.json','parent-CHECK_OPTIMIZED.json']:
  r=load(HERE/'source'/filename);need(r['status']=='PASS'and r['equation_sha256']==PARENT_SHA and r['exact_degree']==312 and r['norm_degree']==256,'completeacceptedparentdegreecertificate')
 rejected=[]
 def reject(bad,label):
  try:verify_map(parent,bad,cert)
  except(ValueError,KeyError,IndexError):rejected.append(label);return
  raise ValueError('mutationaccepted '+label)
 bad=deepcopy(g);i=mapping[parent['named_registers']['Pair']];bad['nodes'][i][0]='add';reject(bad,'wrongguardoperation')
 bad=deepcopy(g);bad['nodes'][bad['output']][0]='mul';reject(bad,'wrongfinalizer')
 bad=deepcopy(g);bad['nodes'][nm['N']][1]=nm['guard'];reject(bad,'normusesprivateguard')
 badcert=deepcopy(cert);badcert['replacement_parent']=parent['named_registers']['Peta']
 try:verify_map(parent,g,badcert)
 except ValueError:rejected.append('wrongguardalias')
 else:raise ValueError('mutatedaliasaccepted')
 exceptional=0
 for q0 in range(-80,81):
  if q0==0 or q0%3==0:continue
  need(gcd(3,2*q0*q0)==1 and q0*q0%(2*q0*q0)!=0,'v0CRTcontradiction');exceptional+=1
 for N in range(-5,6):
  for B in range(-5,6):need((N+B*B+N*B*B==0)==(N==B==0),'unitproductintegercontrol')
 build=load(HERE/'BUILD.json')
 need(sha((ROOT/'tools/build_constructive_integer14_guard_reduced.py').read_bytes())==build['generator_sha256'],'generatorbinding')
 for name,pin in build['sha256'].items():need(sha((HERE/name).read_bytes())==pin,'generatedseal '+name)
 if (HERE/'MANIFEST.json').exists():
  for name,pin in load(HERE/'MANIFEST.json').items():need(sha((HERE/name).read_bytes())==pin,'completepacketseal '+name)
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),integer_variables=14,operations=117,
  operation_counts=dict(counts),exact_degree=312,norm_degree=256,syntactic_bound=344,norm_syntactic_bound=288,
  child_nodes=144,all_nodes_live=True,complete_parent_nodes_accounted=len(parent['nodes']),
  norm_pointwise_identical=True,private_guard_variables_absent_from_norm=True,complete_norm_terms=35,
  guard_difference_degree_bound=20,complete_output_difference_degree_bound=304,whole_six_coefficients=payloads,
  actual_signed_controls=controls,controls_with_changed_outputs=changed,actual_tuple_degree_slices=slices,
  exceptional_CRT_controls=exceptional,rejected_mutations=rejected,equation_sha256=sha((HERE/'equation.json').read_bytes()),
  ordinary_proof_sha256=sha((HERE/'PROOF.md').read_bytes()),parent_equation_sha256=PARENT_SHA,
  scope='Full literal guard substitution and identical norm/core; new ordinary two-way integer-witness proof includingv0. Authentic sixports and complete degree312 topcomponent transfer. No Lean/native/internal-ZFC proof.')
 target=HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json');target.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
