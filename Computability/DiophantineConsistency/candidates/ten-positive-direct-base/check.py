#!/usr/bin/env python3
"""Independent complete direct-base cuts, licensed carrier, norm and degree checks."""
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
PARENT=ROOT/'candidates/ten-positive-short-projection'
PARENT_SHA='cf2748fc277a20a419f196d28674e5374316d5f29fae5ef49c7b113e13b19edd'

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
 need([r['parent_index']for r in records]==list(range(101)),'every101 parentrow accounted')
 expected={4:['X','+','q','x'],36:['qK0X','+','qK0','X'],37:['qK0XC','*','qK0X','C'],38:['B','-','qK0XC','qF'],
  56:['qm1L','*','qbJ','L'],58:['P1','*','q4','bJ'],70:['lowY','*','qbJ','Y'],71:['WBt','*','W','B'],73:['inner0','-','lowY','q3WBt']}
 inserts=[(36,36,'before',['qK0','*','q','K0']),(39,38,'before',['qF','*','q','F']),
  (58,56,'before',['qbJ','*','q','bJ']),(61,58,'before',['q4','*','q3','q']),
  (77,73,'before',['lowX','*','bJ','X']),(79,73,'after',['inner','-','inner0','lowX'])]
 need(cut['changed_parent_indices']==sorted(expected),'allandonly directbase/carrier cuts')
 need(cut['inserted_rows']==[dict(child_index=c,parent_index=p,position=t,row=r)for c,p,t,r in inserts],'exact six inserted definitions')
 children=[]
 for rec in records:
  i=rec['parent_index'];j=rec['child_index'];children.append(j)
  need(rec['old_row']==old[i]and rec['new_row']==rows[j]==expected.get(i,old[i]),'allretained/replaced operandsbound')
  need(rec['status']==('replaced_cut'if i in expected else'retained'),'completecut classification')
  need(j==i+sum(c<=j for c,_,_,_ in inserts),'exactparent/child interleaving')
 for c,_,_,row in inserts:need(rows[c]==row,'actualinserteddefinition');children.append(c)
 need(sorted(children)==list(range(107)),'every107child row exactlyonce')
 need(rows[94:]==old[88:]and cut['child_norm_tail_start']==94,'whole13normtail retained')
 need(child['witnesses']==['x'if n=='w'else n for n in parent['witnesses']]and child['fixed_numerals']==parent['fixed_numerals'],'exactinputreplacement andfourports')

def line_degree(values,p):
 degree=-1;level=0
 while values:
  if values[0]:degree=level
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return degree

def main():
 raw=(HERE/'source/direct-parent-equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'complete frozen101/368 parent')
 parent=json.loads(raw);child=load(HERE/'equation.json');cuts=load(HERE/'CUTS.json');verify_cuts(parent,child,cuts)
 for name,pin in load(PARENT/'MANIFEST.json')['files'].items():need(digest((PARENT/name).read_bytes())==pin,'whole frozen parent seal '+name)
 prov=load(HERE/'PROVENANCE.json')
 for name,pin in prov['dependencies'].items():
  data=(HERE/name).read_bytes();need(data==(ROOT/pin['repository_path']).read_bytes()and digest(data)==pin['sha256'],'whole source binding '+name)
 for name,pin in load(HERE/'BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==pin,'whole generated seal '+name)
 peer_path=HERE/'source/DIRECT_ORDINARY_PEER.json'
 peer=load(peer_path);need(peer['status']=='PASS'and peer['source_pins']['candidates/ten-positive-direct-base/PROOF.md']==digest((HERE/'PROOF.md').read_bytes()),'focused ordinary peer pins current proof')
 rows=child['source'];known=set(child['witnesses']+child['fixed_numerals']);deps={};degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']}
 for n,o,a,b in rows:
  need(n not in known and o in('+','-','*')and all(type(x)is int or x in known for x in(a,b)),'acyclic fresh arithmetic definition')
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b));degrees[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);known.add(n)
 live=set();todo=['N']
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  live.add(v);todo.extend(deps.get(v,()))
 need(live==known,'every107gate/10input/4port live')
 counts=dict(Counter(r[1]for r in rows));need(len(rows)==107 and counts==child['operation_breakdown']=={'*':64,'+':25,'-':18},'actual107 liveoperation count')
 need(child['witnesses']==['J','F','alpha','i','T','x','Y','n','eta','zeta']and child['domain']=='strictly positive integers','precise tenpositive domain')
 need(degrees['N']==child['syntactic_degree']==384 and child['exact_degree']==340,'degree metadata')
 for name,d in child['register_degrees'].items():need(degrees[name]==d,'all actual front degreebounds')
 helper=HERE/'source/independent_norm_oracle.py';need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent sparse norm oracle')
 spec=importlib.util.spec_from_file_location('direct107_oracle',helper);oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 x,a,b,c,extra,omega=[oracle.variable(j)for j in range(6)]
 tail=rows[94:];weighted=oracle.norm_oracle(x,[9*a,b,c]);actual=oracle.evaluate(tail,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N']
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
 centered=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N'];weights=(48,68,70,0,0,85)
 degree=max(sum(e*w for e,w in zip(m,weights))for m in centered.t)
 top={m:c for m,c in centered.t.items()if sum(e*w for e,w in zip(m,weights))==degree}
 need(degree==340 and top=={(0,0,0,0,0,4):1},'unique centeredomega4 leadingweight340')
 # Directbase identities beforeusing anyquotients.
 q,K,w,C,F,L=[oracle.variable(j)for j in range(6)]
 X=q*w;B=(q*K+X)*C-q*F;Bt=(K+w)*C-F
 need((B-q*Bt).t=={},'complete B=qBt ringidentity')
 need((q+(X-q)-X).t=={},'complete basecoordinate identity')
 need(((1+q*(q-1)*L)-(1+(q-1)*L)).t==((q-1)**2*L).t,'exactpositive Wdifference')
 q,Y,W,B,X,unused=[oracle.variable(j)for j in range(6)]
 residue=q*(q-1)*Y-q**3*W*B-(q-1)*X
 need((residue+(q-1)*X).t==(q*((q-1)*Y-q*q*W*B)).t,'wholeprimitivecarrier modqremainder')
 x,a,b,c,extra,omega=[oracle.variable(j)for j in range(6)]
 norm=oracle.evaluate(tail,dict(fs=x,fa=a,fb=b,fc=c))['N']
 scaled=oracle.evaluate(tail,dict(fs=omega*omega*x,fa=omega*omega*a,fb=omega*omega*b,fc=omega*omega*c))['N']
 need(scaled.t==(omega**8*norm).t,'completeweightednorm q8homogeneity')
 saved=oracle.ZERO;oracle.ZERO=(0,)*8
 try:
  def var(j):return oracle.Poly({tuple(int(k==j)for k in range(8)):1})
  q,H,mu,dW,t,u,Bt,X=[var(j)for j in range(8)]
  lhs=H*mu**2*(q**4*(q-1)*(dW*t+u)-q**4*dW*Bt-(q-1)*X)
  rhs=H*mu**2*(q**4*dW*((q-1)*t-Bt)+(q-1)*(q**4*u-X))
  need(lhs.t==rhs.t,'complete universallylicensed numeratorcut includingHmu²')
  q,x,Y,eta,F,alpha,i,K=[var(j)for j in range(8)];X0=q+x;c0=eta*Y;A0=q*q*X0*Y;I0=i*c0*c0;H0=4*A0
  B0=(q*K+X0)*(q-F-alpha)-q*F;R0=q**3*(q-F);Q0=A0**4*I0**2;V0=-A0**2*I0**2*R0
  W0=q*q*H0*I0;Z0=-H0*q**7*W0*B0;M0=H0*q**9;leading=2*Q0*Z0*M0*V0
  factored=2**7*q**39*X0**9*i**5*Y**19*eta**10*B0*(q-F)
  need(leading.t==factored.t,'independentlymultiplied eightvariableleadingproduct')
  maxx=max(m[1]for m in leading.t);need(maxx==10,'omega highestxdegree10')
  topx=oracle.Poly({tuple(0 if j==1 else a for j,a in enumerate(m)):v for m,v in leading.t.items()if m[1]==10})
  need(all(m[7]==0 for m in topx.t),'fullhighestxcomponent independentofK0')
  need((topx**4).t.get((156,0,76,40,4,4,20,0))==2**28,'selected degree340 coefficient includingi20')
 finally:oracle.ZERO=saved
 binding=load(HERE/'coefficients/BINDING.json');need(binding==parent['coefficient_binding']==child['coefficient_binding'],'entire coherentfourport binding')
 coeff={};payloads={}
 for name,pin in binding['ports'].items():
  blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
  need(digest(blob)==pin['gzip_sha256']and digest(raw)==pin['raw_sha256'],'completecompressed/raw payload '+name)
  coeff[name]=int.from_bytes(raw,'little');need(coeff[name].bit_length()==pin['bits'],'exact whole port width');payloads[name]=pin['raw_sha256']
 need(coeff['beta']==2**590069-1 and coeff['beta']>=31 and coeff['K0']>0 and 0<coeff['MC']<coeff['beta']<coeff['MF']<2*coeff['beta'],'all actual uniformport hypotheses')
 rng=random.Random(107340);controls=free_controls=0
 preserved=['X','R','I','Df','Q','delta','V','Dnum','Dtau','L','Kpos']
 def compare(inputs,prime):
  old=evaluate(parent['source'],inputs,prime);q=old['q'];qm=old['bJ']
  if not q or not qm:return False
  changed={n:v for n,v in inputs.items()if n!='w'};changed['x']=(old['X']-q)%prime;new=evaluate(rows,changed,prime)
  need(all(new[n]==old[n]for n in preserved),'fullsameX kernelpreservation')
  need((new['B']-q*old['Bt'])%prime==0 and(new['Mtot']-q*old['Mtot'])%prime==0,'full B/M scalings')
  t=old['Bt']*pow(qm,-1,prime)%prime;u=old['X']*pow(q,-4,prime)%prime
  changed['n']=(inputs['n']+(new['W']-old['W'])*t+u)%prime;restored=evaluate(rows,changed,prime)
  need((restored['Znum']-q*old['Znum'])%prime==0 and(restored['N']-pow(q,8,prime)*old['N'])%prime==0,'licensedcompletecenter/outputscaling')
  return True
 for prime in(1009,(1<<127)-1):
  limit=60 if prime==1009 else 120
  while controls<limit:controls+=compare({v:rng.randrange(-20,21)for v in parent['witnesses']}|{k:v%prime for k,v in coeff.items()},prime)
 for q in(32,64,128):
  for u in(1,2,3):
   w=q**3*u;inputs={v:1 for v in parent['witnesses']}|dict(beta=q-1,K0=(q-2)*(w+1),MC=1,MF=q,w=w,F=q-2)
   old=evaluate(parent['source'],inputs);need(old['Bt']==(q-1)*w,'exactintegerquotient family')
   changed={n:v for n,v in inputs.items()if n!='w'};changed['x']=old['X']-q;new=evaluate(rows,changed)
   changed['n']=inputs['n']+(new['W']-old['W'])*w+u;restored=evaluate(rows,changed)
   need(restored['Znum']==q*old['Znum']and restored['N']==q**8*old['N'],'fullunrestrictedintegercenter/outputscaling');free_controls+=1
 slices=[]
 for prime in((1<<127)-1,(1<<89)-1):
  ports={k:v%prime for k,v in coeff.items()};base={v:rng.randrange(1,prime)for v in child['witnesses']};direction={v:rng.randrange(1,prime)for v in child['witnesses']}
  values=[evaluate(rows,ports|{v:(base[v]+t*direction[v])%prime for v in child['witnesses']},prime)['N']for t in range(386)]
  need(line_degree(values,prime)==340,'wholeactualtuple degree340 line');slices.append(dict(prime_bits=prime.bit_length(),degree=340))
 rejected=[]
 for label,change in [('wrongbase',lambda p:next(r for r in p['source']if r[0]=='X').__setitem__(1,'*')),('wrongcarryterm',lambda p:next(r for r in p['source']if r[0]=='inner').__setitem__(1,'+')),('wrongP',lambda p:next(r for r in p['source']if r[0]=='P1').__setitem__(2,'q3'))]:
  bad=deepcopy(child);change(bad)
  try:verify_cuts(parent,bad,cuts)
  except ValueError:rejected.append(label)
  else:raise ValueError('accepted '+label)
 x,a,b,c,extra,omega=[oracle.variable(j)for j in range(6)]
 bad=deepcopy(tail);bad[-1][1]='+'
 need(oracle.evaluate(bad,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N'].t!=weighted.t,'wholeoutput sign corruptionrejected');rejected.append('normsign')
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,operations=107,
  operation_breakdown=counts,exact_degree=340,syntactic_degree=384,all_parent_child_rows_and_cuts_bound=True,
  whole_provenance_and_parent_seals_checked=True,independent_weightednorm_terms=35,
  inherited_weightednorm_allpositive_identity=True,complete_B_and_W_identities=True,full_licensed_center_cut=True,norm_q8_homogeneity=True,modq_remainder_identity=True,modulus_obstruction=2025,modulus_residue_certificate=[1,2,2],
  unequal_f_y_residual_factorization=True,centered_unique_leading='omega^4, degree340',
  actual_selected_coefficient='2^28*beta^156',actual_selected_monomial=dict(J=156,x=40,i=20,Y=76,eta=40,alpha=4,F=4),
  actual_tuple_kernel_controls=controls,exact_integer_center_controls=free_controls,actual_tuple_degree_slices=slices,
  rejected_semantic_mutations=rejected,whole_four_payloads=payloads,
  ordinary_peer_pins_current_proof=peer_path.exists(),equation_sha256=digest((HERE/'equation.json').read_bytes()),proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
  scope='Complete directbasecuts/primitivecarrier/weightednorm/degree/source binding. Unboundedordinarysign/sourceequivalence is PROOF.md; controlsaretranscriptionchecks. No newLean/internal-ZFC proof; allpagesunchanged.')
 target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
