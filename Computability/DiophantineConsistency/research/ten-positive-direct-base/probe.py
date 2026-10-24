#!/usr/bin/env python3
"""Finite direct-base prototype: literal count, degree and licensed center maps."""
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
def sha(x):return sha256(x).hexdigest()
def enc(x):return(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def evaluate(rows,inputs,p=None):
 e=dict(inputs)
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  r=a+b if o=='+'else a-b if o=='-'else a*b;e[n]=r if p is None else r%p
 return e

def line_degree(values,p):
 d=-1;level=0
 while values:
  if values[0]:d=level
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return d

def main():
 raw=(PARENT/'equation.json').read_bytes();need(sha(raw)==PARENT_SHA,'whole101/368 parent')
 parent=json.loads(raw)
 for n,h in json.loads((PARENT/'MANIFEST.json').read_bytes())['files'].items():need(sha((PARENT/n).read_bytes())==h,'wholeparentseal '+n)
 changes={4:['X','+','q','x'],36:['qK0X','+','qK0','X'],37:['qK0XC','*','qK0X','C'],38:['B','-','qK0XC','qF'],
  56:['qm1L','*','qbJ','L'],58:['P1','*','q4','bJ'],70:['lowY','*','qbJ','Y'],71:['WBt','*','W','B'],
  73:['inner0','-','lowY','q3WBt']}
 before={36:[['qK0','*','q','K0']],38:[['qF','*','q','F']],56:[['qbJ','*','q','bJ']],
  58:[['q4','*','q3','q']],73:[['lowX','*','bJ','X']]}
 after={73:[['inner','-','inner0','lowX']]}
 rows=[];records=[];insertions=[]
 for j,old in enumerate(parent['source']):
  for inserted in before.get(j,[]):insertions.append(dict(child_index=len(rows),row=inserted));rows.append(inserted)
  new=deepcopy(changes.get(j,old));records.append(dict(parent_index=j,child_index=len(rows),old_row=old,new_row=new));rows.append(new)
  for inserted in after.get(j,[]):insertions.append(dict(child_index=len(rows),row=inserted));rows.append(inserted)
 packet=deepcopy(parent);packet.update(name='RESEARCH_direct_positive_base',witnesses=['x'if v=='w'else v for v in parent['witnesses']],source=rows,
  operations=len(rows),operation_breakdown=dict(Counter(r[1]for r in rows)),exact_degree=340,parent_sha256=PARENT_SHA,
  proof_status='Researchordinaryproofunderindependentreview. Finiteprototypeonly; nofrontierpromotion/page/Lean.')
 need(packet['operations']==107 and packet['operation_breakdown']=={'*':64,'+':25,'-':18},'actual107 operations')
 deg={v:1 for v in packet['witnesses']}|{v:0 for v in packet['fixed_numerals']};deps={};known=set(deg)
 for n,o,a,b in rows:
  need(n not in known and all(type(v)is int or v in known for v in(a,b)),'fresh topological row')
  da,db=(0 if type(v)is int else deg[v]for v in(a,b));deg[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);known.add(n)
 live=set();todo=['N']
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(live==known,'all107gates/10vars/4ports live')
 need(deg['N']==384 and all(deg[n]==d for n,d in dict(Am1=4,Dp=8,I=5,Df=18,Q=26,V=22,L=9,W=11,P1=5,Mtot=13,Znum=35,fa=68,fb=70,fc=96,fs=96).items()),'complete actualfront degreebounds')
 packet['register_degrees']={n:deg[n]for n in packet['register_degrees']};packet['syntactic_degree']=384
 helper=PARENT/'source/independent_norm_oracle.py';need(sha(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent normoracle')
 spec=importlib.util.spec_from_file_location('directbase_oracle',helper);o=importlib.util.module_from_spec(spec);spec.loader.exec_module(o)
 x,a,b,c,e,omega=[o.variable(j)for j in range(6)]
 tail=rows[-13:];need(tail==parent['source'][-13:],'entirenormtail unchanged')
 want=o.norm_oracle(x,[9*a,b,c]);need(o.evaluate(tail,dict(fs=x*x,fa=9*a,fb=b,fc=c))['N'].t==want.t,'full35termweightednorm')
 centered=o.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N'];weights=(48,68,70,0,0,85)
 topdegree=max(sum(i*w for i,w in zip(m,weights))for m in centered.t)
 need(topdegree==340 and {m:k for m,k in centered.t.items()if sum(i*w for i,w in zip(m,weights))==340}=={(0,0,0,0,0,4):1},'uniqueomega4degree340')
 # Free numerator identity certifying the primitive carrier denominator.
 q,H,P,Y,W,B=[o.variable(j)for j in range(6)]
 need((q**4*(q-1)).t==(q*(q-1)*q**3).t,'commondenominatorforB')
 # Leading coefficient overeightformalvariables, includingthefreeK0 coefficient.
 saved=o.ZERO;o.ZERO=(0,)*8
 try:
  def var(j):return o.Poly({tuple(int(k==j)for k in range(8)):1})
  q,x,Y,eta,F,alpha,i,K=[var(j)for j in range(8)];X0=q+x;c0=eta*Y;A0=q*q*X0*Y;I0=i*c0*c0;H0=4*A0
  B0=(q*K+X0)*(q-F-alpha)-q*F;R0=q**3*(q-F);Q0=A0**4*I0**2;V0=-A0**2*I0**2*R0
  W0=q*q*H0*I0;Z0=-H0*q**7*W0*B0;M0=H0*q**9;lead=2*Q0*Z0*M0*V0
  expected=2**7*q**39*X0**9*i**5*Y**19*eta**10*B0*(q-F)
  need(lead.t==expected.t,'completeleadingproduct independentlymultiplied')
  maxx=max(m[1]for m in lead.t);need(maxx==10,'highestxomega degree10')
  topx=o.Poly({tuple(0 if j==1 else a for j,a in enumerate(m)):v for m,v in lead.t.items()if m[1]==maxx})
  need(all(m[7]==0 for m in topx.t),'topxcomponent independentofK0')
  need((topx**4).t.get((156,0,76,40,4,4,20,0))==2**28,'selected340coefficientincludingi20')
 finally:o.ZERO=saved
 coeff={};pins={}
 for n,pin in parent['coefficient_binding']['ports'].items():
  blob=(PARENT/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
  need(sha(blob)==pin['gzip_sha256']and sha(raw)==pin['raw_sha256'],'wholeauthenticport '+n);coeff[n]=int.from_bytes(raw,'little');pins[n]=pin
  (HERE/'coefficients').mkdir(exist_ok=True);(HERE/'coefficients'/pin['file']).write_bytes(blob)
 rng=random.Random(107340);controls=0
 for p in(1009,(1<<127)-1):
  while controls<(60 if p==1009 else 120):
   inputs={v:rng.randrange(-20,21)for v in parent['witnesses']}|{n:v%p for n,v in coeff.items()};old=evaluate(parent['source'],inputs,p)
   q=old['q'];qm=old['bJ']
   if not q or not qm:continue
   newinputs={n:v for n,v in inputs.items()if n!='w'};newinputs['x']=(old['X']-q)%p;new=evaluate(rows,newinputs,p)
   preserved=['X','R','I','Df','Q','V','Dnum','Dtau','L','Kpos'];need(all(new[n]==old[n]for n in preserved),'completekernels preserved')
   need((new['B']-q*old['Bt'])%p==0 and(new['Mtot']-q*old['Mtot'])%p==0,'B/M rescalings')
   t=old['Bt']*pow(qm,-1,p)%p;d=old['X']*pow(q, -4,p)%p
   newinputs['n']=(inputs['n']+(new['W']-old['W'])*t+d)%p;restored=evaluate(rows,newinputs,p)
   need((restored['Znum']-q*old['Znum'])%p==0 and(restored['N']-pow(q,8,p)*old['N'])%p==0,'completequotientlicensedoutput scaling');controls+=1
 slices=[]
 for p in((1<<127)-1,(1<<89)-1):
  ports={n:v%p for n,v in coeff.items()};base={v:rng.randrange(1,p)for v in packet['witnesses']};direction={v:rng.randrange(1,p)for v in packet['witnesses']}
  vals=[evaluate(rows,ports|{v:(base[v]+t*direction[v])%p for v in packet['witnesses']},p)['N']for t in range(386)]
  need(line_degree(vals,p)==340,'actualtupledegree340line');slices.append(dict(prime_bits=p.bit_length(),degree=340))
 need(all(5*r-30>4*r+4 for r in range(35,1000)),'finiteheightboundary diagnostics')
 need(all(4*k<=2**k for k in range(4,100)),'powerboundary diagnostics')
 (HERE/'PROVENANCE.json').write_bytes(enc(dict(parent_equation_sha256=PARENT_SHA,parent_manifest_sha256=sha((PARENT/'MANIFEST.json').read_bytes()),parent_proof_sha256=sha((PARENT/'PROOF.md').read_bytes()),parent_repository_path='candidates/ten-positive-short-projection',whole_original_compact44_tuple=True,probe_sha256=sha(Path(__file__).read_bytes()))))
 (HERE/'prototype-equation.json').write_bytes(enc(packet));(HERE/'PREFIX_MAP.json').write_bytes(enc(dict(parent_rows=records,insertions=insertions)))
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),research_only=True,operations=107,operation_breakdown=packet['operation_breakdown'],positive_unknowns=10,
  exact_degree=340,syntactic_degree=384,complete_source_graph_live=True,independent_weightednorm_terms=35,
  selected_coefficient='2^28*beta^156',selected_monomial=dict(J=156,x=40,i=20,Y=76,eta=40,alpha=4,F=4),
  quotientlicensed_modular_controls=controls,actual_tuple_degree_slices=slices,whole_parent_equation_sha256=PARENT_SHA,
  whole_four_port_pins=pins,proof_sha256=sha((HERE/'PROOF.md').read_bytes()),equation_sha256=sha((HERE/'prototype-equation.json').read_bytes()),
  scope='Finiteprototype/count/leadingcertificate andactualtuplecontrols; ordinaryproofunderindependentreview, nofrontier/page/Leanpromotion.')
 (HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json')).write_bytes(enc(report));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
