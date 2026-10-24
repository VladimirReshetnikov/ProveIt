#!/usr/bin/env python3
"""Independent full short-projection cuts, ring identities, norm and degree checks."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'candidates/ten-positive-weighted-roots'
PARENT_SHA='dea8cdd2489b6797188335f0984cb8ac423f316d22966a149ab592f0cb91e192'

def need(ok,text):
 if not ok:raise ValueError(text)
def digest(x):return sha256(x).hexdigest()
def load(p):return json.loads(p.read_bytes())
def evaluate(rows,inputs,p=None):
 env=dict(inputs)
 for n,o,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  z=a+b if o=='+'else a-b if o=='-'else a*b;env[n]=z if p is None else z%p
 return env

def verify_cuts(parent,child,cut):
 old,rows=parent['source'],child['source'];records=cut['all_parent_rows']
 need([r['parent_index']for r in records]==list(range(102)),'every parent row accounted')
 expected={64:['threec','*',3,'c'],65:['twoX','*',2,'X'],66:['gap','-','threec','twoX'],
  67:['Kpos0','*','X','gap'],68:['Kpos','+','Kpos0',2],69:['lin','+','Hn','Kpos']}
 need(cut['deleted_parent_indices']==[18]and cut['changed_parent_indices']==sorted(expected),'only exactprivate/projection cuts')
 children=[]
 for rec in records:
  i=rec['parent_index'];need(rec['old_row']==old[i],'every original definition')
  if i==18:
   need(old[i]==['ap','-','Am1',1]and rec['status']=='deleted_private','only privateap subtractedgate deleted');continue
  j=rec['child_index'];children.append(j)
  need(rec['new_row']==rows[j]==expected.get(i,old[i]),'all retained/replaced operands')
  need(rec['status']==('replaced_cut'if i in expected else'retained'),'complete cutclassification')
 need(children==list(range(101)),'every child row exactly once')
 need([i for i,r in enumerate(old)if'ap'in r[2:]]==[64],'deletedap has no otherconsumer')
 need(rows[88:]==old[89:]and cut['child_norm_tail_start']==88,'entire13gate normtail unchanged')
 need(child['witnesses']==parent['witnesses']and child['fixed_numerals']==parent['fixed_numerals'],'complete input/fixedport lists')

def line_degree(values,p):
 degree=-1;level=0
 while values:
  if values[0]:degree=level
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return degree

def main():
 raw=(HERE/'source/projection-parent-equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'complete frozen102/368 parent')
 parent=json.loads(raw);child=load(HERE/'equation.json');cuts=load(HERE/'CUTS.json');verify_cuts(parent,child,cuts)
 for name,pin in load(PARENT/'MANIFEST.json')['files'].items():need(digest((PARENT/name).read_bytes())==pin,'whole frozen parent seal '+name)
 prov=load(HERE/'PROVENANCE.json')
 for name,pin in prov['dependencies'].items():
  data=(HERE/name).read_bytes();need(data==(ROOT/pin['repository_path']).read_bytes()and digest(data)==pin['sha256'],'whole source binding '+name)
 for name,pin in load(HERE/'BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==pin,'whole generated seal '+name)
 peer_path=HERE/'source/SHORT_ORDINARY_PEER.json'
 peer=load(peer_path);need(peer['status']=='PASS'and peer['source_pins']['candidates/ten-positive-short-projection/PROOF.md']==digest((HERE/'PROOF.md').read_bytes()),'focused ordinary peer pins current proof')
 rows=child['source'];known=set(child['witnesses']+child['fixed_numerals']);deps={};degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  need(n not in known and o in('+','-','*')and all(type(x)is int or x in known for x in(a,b)),'acyclic fresh arithmetic definition')
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);known.add(n)
 live=set();todo=['N']
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  live.add(v);todo.extend(deps.get(v,()))
 need(live==known,'every101gate/10input/4port live')
 counts=dict(Counter(r[1]for r in rows));need(len(rows)==101 and counts==child['operation_breakdown']=={'*':60,'+':24,'-':17},'actual101 liveoperation count')
 need(child['witnesses']==['J','F','alpha','i','T','w','Y','n','eta','zeta']and child['domain']=='strictly positive integers','precise tenpositive domain')
 need(degrees['N']==child['syntactic_degree']==416 and child['exact_degree']==368,'degree metadata')
 for name,d in child['register_degrees'].items():need(degrees[name]==d,'all actual front degreebounds')
 helper=HERE/'source/independent_norm_oracle.py';need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent sparse norm oracle')
 spec=importlib.util.spec_from_file_location('short101_oracle',helper);oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 x,a,b,c,extra,omega=[oracle.variable(j)for j in range(6)]
 tail=rows[88:];weighted=oracle.norm_oracle(x,[9*a,b,c]);actual=oracle.evaluate(tail,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N']
 need(actual.t==weighted.t and len(weighted.t)==35,'all35 independent weightednorm coefficients')
 roots=oracle.evaluate(tail,dict(fs=(3*a+b+c)**2,fa=9*a*a,fb=b*b,fc=c*c))['N']
 need(roots.t=={},'universal allpositive root-map polynomial identity')
 def sub(poly,vals):return sum(coef*__import__('functools').reduce(lambda z,p:z*p,(v**e for v,e in zip(vals,m)),1)for m,coef in poly.t.items())
 need(sub(weighted,(0,1,1,1,0,0))==2025==3**4*5**2,'exact complete triple obstruction')
 need([(q*q+1)%3 for q in range(3)]==[1,2,2],'complete residuecertificate gcd(q²+1,3)=1')
 need([9-1,9-1]==[8,8]and 32**2+1>25,'pair/triple integer modulus bounds')
 d,I,V=x,a,b;df=1+d*I*I;Q=d*d*I*I
 need((Q*(V*V-df)+(df-1)).t==(d*I*I*(d*(V*V-df)+1)).t,'complete residualfactor f=y obstruction before rationality')
 A,X,c,n,u,unused=[oracle.variable(j)for j in range(6)]
 H=4*A-5;Kold=X*(X+2*(A-2)*c)-1;Kpos=X*(3*c-2*X)+2
 need(Kpos.t==(H*X*c-2*Kold).t,'complete projectionidentity overfreeintegers')
 need((3*Kold-H*X*c).t==(3*(X*X-1)+(2*A-7)*X*c).t,'strictpositive witnessdifference identity')
 need((H*(n+3*u-X*c)+Kpos-(H*n+Kold)).t==(3*(H*u-Kold)).t,'universal fullcentercut with suppliedquotient')
 x,a,b,c,extra,omega=[oracle.variable(j)for j in range(6)]
 centered=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N'];weights=(52,74,76,0,0,92)
 degree=max(sum(e*w for e,w in zip(m,weights))for m in centered.t)
 top={m:c for m,c in centered.t.items()if sum(e*w for e,w in zip(m,weights))==degree}
 need(degree==368 and top=={(0,0,0,0,0,4):1},'unique centeredomega4 leadingweight368')
 # Independently bound the entire output change, not only its selected monomial.
 need(degrees['P1mu2']==8 and degrees['Kpos']==4 and parent['register_degrees']['Kquad']==9,'actual projection contribution bounds')
 dz=degrees['P1mu2']+max(degrees['Kpos'],parent['register_degrees']['Kquad'])
 ds=degrees['delta']+dz+max(degrees['Znum'],parent['register_degrees']['Znum'],dz)
 need((dz,ds)==(17,84),'complete Z and squaredcenter difference bounds')
 before=oracle.evaluate(tail,dict(fs=c+omega,fa=a,fb=b,fc=c))['N']
 after=oracle.evaluate(tail,dict(fs=c+omega+extra,fa=a,fb=b,fc=c))['N']
 difference=after-before;difference_weights=(0,74,76,104,ds,92)
 difference_degree=max(sum(e*w for e,w in zip(m,difference_weights))for m in difference.t)
 need(difference_degree==360<368,'complete universal polynomialdifference lowerdegree than retainedleadingform')
 # A seven-variable independent leading-form product, including theactual i exponent.
 saved=oracle.ZERO;oracle.ZERO=(0,)*7
 try:
  def var7(j):return oracle.Poly({tuple(int(k==j)for k in range(7)):1})
  q,w,Y,eta,F,alpha,i=[var7(j)for j in range(7)]
  A0=q*q*(q*w*Y);I0=i*(eta*Y)**2;R0=q**3*(q-F);Bt0=w*(q-F-alpha);H0=4*A0
  Q0=A0**4*I0**2;V00=-A0**2*I0**2*R0;W0=q*H0*I0;Z00=-H0*q**7*W0*Bt0;M0=H0*q**8
  leading=2*Q0*Z00*M0*V00
  factored=2**7*q**46*i**5*w**10*Y**19*eta**10*(q-F-alpha)*(q-F)
  need(leading.t==factored.t,'independent complete leadingproduct multiplication at zeta0')
  need((leading**4).t.get((184,40,76,40,4,4,20))==2**28,'actual selected leading coefficient, includingi20')
 finally:oracle.ZERO=saved
 binding=load(HERE/'coefficients/BINDING.json');need(binding==parent['coefficient_binding']==child['coefficient_binding'],'entire coherentfourport binding')
 coeff={};payloads={}
 for name,pin in binding['ports'].items():
  blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
  need(digest(blob)==pin['gzip_sha256']and digest(raw)==pin['raw_sha256'],'completecompressed/raw payload '+name)
  coeff[name]=int.from_bytes(raw,'little');need(coeff[name].bit_length()==pin['bits'],'exact whole port width');payloads[name]=pin['raw_sha256']
 need(coeff['beta']==2**590069-1 and coeff['beta']>=31 and coeff['K0']>0 and 0<coeff['MC']<coeff['beta']<coeff['MF']<2*coeff['beta'],'all actual uniformport hypotheses')
 rng=random.Random(101368);controls=free_controls=restored_modular=restored_integer=0
 preserved=['I','Df','Q','delta','V','Dnum','Dtau','L','W','Mtot','fa','fb','fc']
 def compare(inputs,prime=None):
  old=evaluate(parent['source'],inputs,prime);new=evaluate(rows,inputs,prime)
  def equal(a,b):return a==b if prime is None else(a-b)%prime==0
  need(all(old[n]==new[n]for n in preserved),'all kernel/radicand/transport registers retained')
  need(equal(new['Kpos'],old['Hp']*old['X']*old['c']-2*old['Kquad']),'whole actualprojectionidentity')
  need(equal(new['Znum']-old['Znum'],old['P1mu2']*(new['Kpos']-old['Kquad'])),'whole actualcarrier difference')
  s,u,v,w=new['fs'],old['fa'],old['fb'],old['fc'];norm=((s+w-u-v)**2-4*(s*w+u*v))**2-64*s*w*u*v
  need(equal(new['N'],norm),'complete output at changedcenter')
  H=old['Hp'];q=None
  if prime is not None and H%prime:q=old['Kquad']*pow(H,-1,prime)%prime
  if prime is None and H and old['Kquad']%H==0:q=old['Kquad']//H
  if q is not None:
   changed=dict(inputs);changed['n']=inputs['n']+3*q-old['X']*old['c'];restored=evaluate(rows,changed,prime)
   need(equal(restored['Znum'],old['Znum'])and equal(restored['N'],old['N']),'fullquotientlicensed centermap/outputidentity')
   return True
  return False
 for prime in(1009,(1<<127)-1):
  for _ in range(60):
   restored_modular+=compare({v:rng.randrange(-20,21)for v in parent['witnesses']}|{k:v%prime for k,v in coeff.items()},prime);controls+=1
 for _ in range(50):
  restored_integer+=compare({v:rng.randrange(-2,3)for v in parent['witnesses']+parent['fixed_numerals']});free_controls+=1
 slices=[]
 for prime in((1<<127)-1,(1<<89)-1):
  ports={k:v%prime for k,v in coeff.items()};base={v:rng.randrange(1,prime)for v in child['witnesses']};direction={v:rng.randrange(1,prime)for v in child['witnesses']}
  values=[evaluate(rows,ports|{v:(base[v]+t*direction[v])%prime for v in child['witnesses']},prime)['N']for t in range(418)]
  need(line_degree(values,prime)==368,'wholeactualtuple degree368 line');slices.append(dict(prime_bits=prime.bit_length(),degree=368))
 rejected=[]
 for label,change in [('wrongprojectioncoefficient',lambda p:next(r for r in p['source']if r[0]=='threec').__setitem__(2,4)),('wrongprojectionsign',lambda p:next(r for r in p['source']if r[0]=='gap').__setitem__(1,'+'))]:
  bad=deepcopy(child);change(bad)
  try:verify_cuts(parent,bad,cuts)
  except ValueError:rejected.append(label)
  else:raise ValueError('accepted '+label)
 bad=deepcopy(tail);bad[-1][1]='+'
 need(oracle.evaluate(bad,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N'].t!=weighted.t,'wholeoutput sign corruptionrejected');rejected.append('normsign')
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,operations=101,
  operation_breakdown=counts,exact_degree=368,syntactic_degree=416,all_parent_child_rows_and_cuts_bound=True,
  whole_provenance_and_parent_seals_checked=True,independent_weightednorm_terms=35,
  inherited_weightednorm_allpositive_identity=True,full_universal_projection_and_center_cuts=True,modulus_obstruction=2025,modulus_residue_certificate=[1,2,2],
  unequal_f_y_residual_factorization=True,centered_unique_leading='omega^4, degree368',
  projection_center_difference_degree_bound=dz,squared_center_difference_degree_bound=ds,whole_output_difference_degree_bound=difference_degree,
  actual_selected_coefficient='2^28*beta^184',actual_selected_monomial=dict(J=184,i=20,w=40,Y=76,eta=40,alpha=4,F=4),
  actual_tuple_kernel_controls=controls,exact_free_signed_port_controls=free_controls,restored_modular_centers=restored_modular,restored_integer_centers=restored_integer,actual_tuple_degree_slices=slices,
  rejected_semantic_mutations=rejected,whole_four_payloads=payloads,
  ordinary_peer_pins_current_proof=peer_path.exists(),equation_sha256=digest((HERE/'equation.json').read_bytes()),proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
  scope='Complete literal/projector/carrier/norm/modulus/degree/source binding. Unboundedordinarysign/sourceequivalence is PROOF.md; controlsaretranscriptionchecks. No newLean/internal-ZFC proof; allpagesunchanged.')
 target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
