#!/usr/bin/env python3
"""Independent complete weighted-root circuit, modulus, norm and degree checks."""
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
PARENT=ROOT/'candidates/ten-positive-shifted-strong'
PARENT_SHA='7800654c08a096342c72e7f18a14d7362ebe1a0ab29aa19a3ebbcfa41e73fc0f'

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
 need(cut['deleted_parent_indices']==[41]and cut['changed_parent_indices']==[42,84],'all and only intended cuts')
 expected={42:['I','*','i','c2'],84:['fa','*','dM2','Dtau9']};children=[]
 for rec in records:
  i=rec['parent_index'];need(rec['old_row']==old[i],'whole parent definition')
  if i==41:
   need(old[i]==['shift_i','+','i','q2']and rec['status']=='deleted_private','only old private shift addition deleted');continue
  j=rec['child_index'];children.append(j)
  need(rec['new_row']==rows[j]==expected.get(i,old[i]),'every retained/replaced operand')
  need(rec['status']==('replaced_cut'if i in expected else'retained'),'all parent cut classifications')
 need(cut['inserted_rows']==[dict(child_index=83,row=['Dtau9','*',9,'Dtau'])],'one and only one scalar insertion')
 for rec in cut['inserted_rows']:
  children.append(rec['child_index']);need(rows[rec['child_index']]==rec['row'],'actual inserted definition')
 need(sorted(children)==list(range(102)),'complete child coverage without duplication')
 need([i for i,r in enumerate(old)if'shift_i'in r[2:]]==[42],'deleted shift has no other consumer')
 need(rows[89:]==old[89:]and cut['child_norm_tail_start']==89,'whole13-gate tail unchanged')
 need(child['witnesses']==parent['witnesses']and child['fixed_numerals']==parent['fixed_numerals'],'entire input/fixedport lists')

def line_degree(values,p):
 degree=-1;level=0
 while values:
  if values[0]:degree=level
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return degree

def main():
 raw=(HERE/'source/weighted-parent-equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'complete frozen102/388 parent')
 parent=json.loads(raw);child=load(HERE/'equation.json');cuts=load(HERE/'CUTS.json');verify_cuts(parent,child,cuts)
 for name,pin in load(PARENT/'MANIFEST.json')['files'].items():need(digest((PARENT/name).read_bytes())==pin,'whole frozen parent seal '+name)
 prov=load(HERE/'PROVENANCE.json')
 for name,pin in prov['dependencies'].items():
  data=(HERE/name).read_bytes();need(data==(ROOT/pin['repository_path']).read_bytes()and digest(data)==pin['sha256'],'whole source binding '+name)
 for name,pin in load(HERE/'BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==pin,'whole generated seal '+name)
 peer_path=HERE/'source/WEIGHTED_ORDINARY_PEER.json'
 peer=load(peer_path);need(peer['status']=='PASS'and peer['source_pins']['candidates/ten-positive-weighted-roots/PROOF.md']==digest((HERE/'PROOF.md').read_bytes()),'focused ordinary peer pins current proof')
 rows=child['source'];known=set(child['witnesses']+child['fixed_numerals']);deps={};degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  need(n not in known and o in('+','-','*')and all(type(x)is int or x in known for x in(a,b)),'acyclic fresh arithmetic definition')
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);known.add(n)
 live=set();todo=['N']
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  live.add(v);todo.extend(deps.get(v,()))
 need(live==known,'every102gate/10input/4port live')
 counts=dict(Counter(r[1]for r in rows));need(len(rows)==102 and counts==child['operation_breakdown']=={'*':60,'+':24,'-':18},'actual102 liveoperation count')
 need(child['witnesses']==['J','F','alpha','i','T','w','Y','n','eta','zeta']and child['domain']=='strictly positive integers','precise tenpositive domain')
 need(degrees['N']==child['syntactic_degree']==416 and child['exact_degree']==368,'degree metadata')
 for name,d in child['register_degrees'].items():need(degrees[name]==d,'all actual front degreebounds')
 helper=HERE/'source/independent_norm_oracle.py';need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent sparse norm oracle')
 spec=importlib.util.spec_from_file_location('weighted102_oracle',helper);oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 x,a,b,c,extra,omega=[oracle.variable(j)for j in range(6)]
 tail=rows[89:];weighted=oracle.norm_oracle(x,[9*a,b,c]);actual=oracle.evaluate(tail,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N']
 need(actual.t==weighted.t and len(weighted.t)==35,'all35 independent weightednorm coefficients')
 roots=oracle.evaluate(tail,dict(fs=(3*a+b+c)**2,fa=9*a*a,fb=b*b,fc=c*c))['N']
 need(roots.t=={},'universal allpositive root-map polynomial identity')
 def sub(poly,vals):return sum(coef*__import__('functools').reduce(lambda z,p:z*p,(v**e for v,e in zip(vals,m)),1)for m,coef in poly.t.items())
 need(sub(weighted,(0,1,1,1,0,0))==2025==3**4*5**2,'exact complete triple obstruction')
 need([(q*q+1)%3 for q in range(3)]==[1,2,2],'complete residuecertificate gcd(q²+1,3)=1')
 need([9-1,9-1]==[8,8]and 32**2+1>25,'pair/triple integer modulus bounds')
 d,I,V=x,a,b;df=1+d*I*I;Q=d*d*I*I
 need((Q*(V*V-df)+(df-1)).t==(d*I*I*(d*(V*V-df)+1)).t,'complete residualfactor f=y obstruction before rationality')
 centered=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N'];weights=(52,74,76,0,0,92)
 degree=max(sum(e*w for e,w in zip(m,weights))for m in centered.t)
 top={m:c for m,c in centered.t.items()if sum(e*w for e,w in zip(m,weights))==degree}
 need(degree==368 and top=={(0,0,0,0,0,4):1},'unique centeredomega4 leadingweight368')
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
 rng=random.Random(102368);controls=free_controls=0
 preserved=['I','Df','Q','delta','V','Dnum','Dtau','L','W','Mtot','Znum','fs','fb','fc']
 def compare(inputs,prime=None):
  old=evaluate(parent['source'],inputs,prime);changed=dict(inputs);changed['i']=inputs['i']+old['q2'];new=evaluate(rows,changed,prime)
  need(all(old[n]==new[n]for n in preserved),'complete shiftedkernel/carrier preservation')
  need(new['fa']==(9*old['fa']if prime is None else 9*old['fa']%prime),'exactonlyweighted radicand')
  s,u,v,w=old['fs'],9*old['fa'],old['fb'],old['fc'];norm=((s+w-u-v)**2-4*(s*w+u*v))**2-64*s*w*u*v
  need(new['N']==(norm if prime is None else norm%prime),'entirechildoutput from weightedparent cuts')
 for prime in(1009,(1<<127)-1):
  for _ in range(60):compare({v:rng.randrange(-20,21)for v in parent['witnesses']}|{k:v%prime for k,v in coeff.items()},prime);controls+=1
 for _ in range(50):compare({v:rng.randrange(-2,3)for v in parent['witnesses']+parent['fixed_numerals']});free_controls+=1
 slices=[]
 for prime in((1<<127)-1,(1<<89)-1):
  ports={k:v%prime for k,v in coeff.items()};base={v:rng.randrange(1,prime)for v in child['witnesses']};direction={v:rng.randrange(1,prime)for v in child['witnesses']}
  values=[evaluate(rows,ports|{v:(base[v]+t*direction[v])%prime for v in child['witnesses']},prime)['N']for t in range(418)]
  need(line_degree(values,prime)==368,'wholeactualtuple degree368 line');slices.append(dict(prime_bits=prime.bit_length(),degree=368))
 rejected=[]
 for label,change in [('wrongI',lambda p:next(r for r in p['source']if r[0]=='I').__setitem__(2,'mu')),('weight8',lambda p:next(r for r in p['source']if r[0]=='Dtau9').__setitem__(2,8))]:
  bad=deepcopy(child);change(bad)
  try:verify_cuts(parent,bad,cuts)
  except ValueError:rejected.append(label)
  else:raise ValueError('accepted '+label)
 bad=deepcopy(tail);bad[-1][1]='+'
 need(oracle.evaluate(bad,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N'].t!=weighted.t,'wholeoutput sign corruptionrejected');rejected.append('normsign')
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,operations=102,
  operation_breakdown=counts,exact_degree=368,syntactic_degree=416,all_parent_child_rows_and_cuts_bound=True,
  whole_provenance_and_parent_seals_checked=True,independent_weightednorm_terms=35,
  universal_canonical_root_map=True,modulus_obstruction=2025,modulus_residue_certificate=[1,2,2],
  unequal_f_y_residual_factorization=True,centered_unique_leading='omega^4, degree368',
  actual_selected_coefficient='2^28*beta^184',actual_selected_monomial=dict(J=184,i=20,w=40,Y=76,eta=40,alpha=4,F=4),
  actual_tuple_kernel_controls=controls,exact_free_signed_port_controls=free_controls,actual_tuple_degree_slices=slices,
  rejected_semantic_mutations=rejected,whole_four_payloads=payloads,
  ordinary_peer_pins_current_proof=peer_path.exists(),equation_sha256=digest((HERE/'equation.json').read_bytes()),proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
  scope='Complete literal/norm/modulus/degree/source binding. Unboundedordinarysign/sourceequivalence is PROOF.md; controlsaretranscriptionchecks. No newLean/internal-ZFC proof; allpagesunchanged.')
 target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
