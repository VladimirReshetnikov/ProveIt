#!/usr/bin/env python3
"""Independent two-cut/input-map, octic, centered-degree and tuple checker."""
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
PARENT=ROOT/'candidates/ten-positive-free-j'
PARENT_SHA='1b20a25bddd6c494222c19d74142b53960f18b39be9fe323b49a4e5667e4d318'

def need(ok,message):
 if not ok:raise ValueError(message)
def digest(x):return sha256(x).hexdigest()
def load(p):return json.loads(p.read_bytes())
def evaluate(rows,inputs,p=None):
 env=dict(inputs)
 for n,o,a,b in rows:
  a=a if type(a)is int else env[a];b=b if type(b)is int else env[b]
  v=a+b if o=='+'else a-b if o=='-'else a*b;env[n]=v if p is None else v%p
 return env

def verify_cuts(parent,child,cut):
 old,rows=parent['source'],child['source'];records=cut['all_parent_rows']
 need([r['parent_index']for r in records]==list(range(103)),'every parent row accounted')
 expected={41:['shift_i','+','i','q2'],42:['I','*','shift_i','c2'],56:['HI','*','Hp','I'],58:['L','+','HI','cTR']}
 need(cut['changed_parent_indices']==sorted(expected)and cut['deleted_parent_indices']==[57],'precise changed cuts')
 children=[]
 for rec in records:
  i=rec['parent_index'];need(rec['old_row']==old[i],'every original definition pinned')
  if i==57:
   need(rec['status']=='deleted_private'and old[i]==['L1','+','cTR','cT'],'only private old L addition deleted');continue
  j=rec['child_index'];children.append(j)
  need(rec['new_row']==rows[j]==expected.get(i,old[i]),'all retained/replaced rows and operands bound')
  need(rec['status']==('replaced_cut'if i in expected else'retained'),'complete status classification')
 need(children==list(range(102)),'every child row accounted exactly once')
 for name,uses in [('muc2',[42]),('4Am1I',[58]),('L1',[58])]:
  need([i for i,r in enumerate(old)if name in r[2:]]==uses,'removed private name only feeds its declared cut')
 need(old[10]==['q2','*','q','q']and old[11]==['mu','+','q2',1], 'actual cached q²/mu relation')
 need(child['witnesses']==parent['witnesses']and child['fixed_numerals']==parent['fixed_numerals'],'all ten inputs and four fixedports retained')

def line_degree(values,p):
 degree=-1;level=0;values=list(values)
 while values:
  if values[0]:degree=level
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return degree

def main():
 raw=(HERE/'source/shift-parent-equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'whole frozen103 parent')
 parent=json.loads(raw);child=load(HERE/'equation.json');cuts=load(HERE/'CUTS.json');verify_cuts(parent,child,cuts)
 for n,h in load(PARENT/'MANIFEST.json')['files'].items():need(digest((PARENT/n).read_bytes())==h,'entire parent seal '+n)
 provenance=load(HERE/'PROVENANCE.json')
 for name,pin in provenance['dependencies'].items():
  data=(HERE/name).read_bytes();need(data==(ROOT/pin['repository_path']).read_bytes()and digest(data)==pin['sha256'],'whole pinned dependency '+name)
 peer=load(HERE/'source/SHIFTED_ORDINARY_PEER.json');need(peer['status']=='PASS'and peer['source_pins']['candidates/ten-positive-shifted-strong/PROOF.md']==digest((HERE/'PROOF.md').read_bytes()),'focused ordinary peer pins exact current proof')
 for n,h in load(HERE/'BUILD.json')['sha256'].items():need(digest((HERE/n).read_bytes())==h,'generated seal '+n)
 rows=child['source'];known=set(child['witnesses']+child['fixed_numerals']);deps={};degs={x:1 for x in child['witnesses']}|{x:0 for x in child['fixed_numerals']}
 for n,o,a,b in rows:
  need(n not in known and o in('+','-','*')and all(type(x)is int or x in known for x in(a,b)),'fresh acyclic arithmetic gate')
  da,db=(0 if type(x)is int else degs[x]for x in(a,b));degs[n]=da+db if o=='*'else max(da,db);known.add(n);deps[n]=(a,b)
 live=set();todo=['N']
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  live.add(v);todo.extend(deps.get(v,()))
 need(live==known,'all102 gates/10inputs/4ports live')
 counts=dict(Counter(r[1]for r in rows));need(counts==child['operation_breakdown']=={'*':59,'+':25,'-':18}and len(rows)==102,'actual102 operations')
 need(child['domain']=='strictly positive integers'and degs['N']==child['syntactic_degree']==440 and child['exact_degree']==388,'precise domain and degreecontracts')
 for n,d in child['register_degrees'].items():need(degs[n]==d,'all stated front degreebounds')
 helper=HERE/'source/independent_norm_oracle.py';need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent oracle')
 spec=importlib.util.spec_from_file_location('shifted_strong102_oracle',helper);oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 x,a,b,c,h,omega=[oracle.variable(i)for i in range(6)]
 # Three distinct universal cut identities; no positivity is inferred here.
 oldI=x*(a*a+1)*c*c;newI=((a*a+1)*x-a*a+a*a)*c*c
 need(oldI.t==newI.t,'entire shiftedI polynomial map')
 oldL=4*x*a+b+c;newL=(4*x-1)*a+b
 need((oldL-newL).t==(a+c).t,'entire shorterL identity including missingI term')
 q3,qm,mu2,H,shift,Bt=[oracle.variable(i)for i in range(6)]
 need((q3*qm*mu2*H*(-shift*Bt)-H*mu2*q3*(-qm*shift)*Bt).t=={},'entire carrier input-map cancellation')
 x,a,b,c,_,omega=[oracle.variable(i)for i in range(6)]
 tail=rows[89:];want=oracle.norm_oracle(x,[a,b,c]);actual=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=c))['N']
 need(len(tail)==13 and tail==parent['source'][90:]and actual.t==want.t and len(want.t)==35,'whole independent35-term octic')
 centered=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N'];weights=(55,76,80,0,0,97)
 d=max(sum(i*w for i,w in zip(m,weights))for m in centered.t);top={m:v for m,v in centered.t.items()if sum(i*w for i,w in zip(m,weights))==d}
 need(d==388 and top=={(0,0,0,0,0,4):1},'unique centereddegree388 leadingomega4')
 q,w,Y,eta,F,alpha=[oracle.variable(i)for i in range(6)]
 lead=2**28*q**224*w**40*Y**76*eta**40*(q-F-alpha)**4*(q-F)**4
 need(lead.t.get((224,40,76,40,4,4))==2**28,'selected homogeneous coefficient before q=betaJ')
 coeff={};payloads={};binding=load(HERE/'coefficients/BINDING.json')
 need(binding==parent['coefficient_binding']==child['coefficient_binding'],'entire coefficientbinding unchanged')
 for name,pin in binding['ports'].items():
  blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
  need(digest(blob)==pin['gzip_sha256']and digest(raw)==pin['raw_sha256'],'whole actual coefficient '+name)
  coeff[name]=int.from_bytes(raw,'little');need(coeff[name].bit_length()==pin['bits'],'whole port width');payloads[name]=pin['raw_sha256']
 need(coeff['beta']==2**590069-1 and coeff['beta']>=31 and coeff['K0']>0 and 0<coeff['MC']<coeff['beta']<coeff['MF']<2*coeff['beta'],'whole authentic uniformbox')
 rng=random.Random(102388);actual_controls=free_controls=0
 targets=['I','Df','Q','delta','V','Dnum','Dtau','Mtot','Znum','fs','fa','fb','fc','N']
 for prime in(1009,(1<<127)-1):
  ports={k:v%prime for k,v in coeff.items()}
  for _ in range(60):
   inputs={v:rng.randrange(-20,21)for v in parent['witnesses']};inputs.update(ports)
   old=evaluate(parent['source'],inputs,prime);newinputs=dict(inputs)
   newinputs['i']=(old['mu']*inputs['i']-old['q2'])%prime
   newinputs['n']=(inputs['n']-(old['I']+old['cT'])*old['Bt'])%prime
   new=evaluate(rows,newinputs,prime)
   need(all(old[k]==new[k]for k in targets),'allcore/carrier/radicands/output preserved under exact fullinputmap')
   need((old['L']-new['L']-old['I']-old['cT'])%prime==0 and
        (old['W']-new['W']-old['bJ']*(old['I']+old['cT']))%prime==0,'actual shorterL/W differences')
   actual_controls+=1
 for _ in range(50):
  inputs={v:rng.randrange(-2,3)for v in parent['witnesses']+parent['fixed_numerals']};old=evaluate(parent['source'],inputs)
  newinputs=dict(inputs);newinputs['i']=old['mu']*inputs['i']-old['q2'];newinputs['n']=inputs['n']-(old['I']+old['cT'])*old['Bt'];new=evaluate(rows,newinputs)
  need(all(old[k]==new[k]for k in targets),'exact signed free-port fullinputmap');free_controls+=1
 slices=[]
 for prime in((1<<127)-1,(1<<89)-1):
  ports={k:v%prime for k,v in coeff.items()};base={v:rng.randrange(1,prime)for v in child['witnesses']};direction={v:rng.randrange(1,prime)for v in child['witnesses']}
  vals=[evaluate(rows,ports|{v:(base[v]+t*direction[v])%prime for v in child['witnesses']},prime)['N']for t in range(442)]
  need(line_degree(vals,prime)==388,'whole actual tupledegree388 slice');slices.append(dict(prime_bits=prime.bit_length(),degree=388))
 bad=deepcopy(child);bad['source'][41][1]='*'
 try:verify_cuts(parent,bad,cuts)
 except ValueError:pass
 else:raise ValueError('actual shiftedI mutation accepted')
 bad=deepcopy(tail);bad[-1][1]='+'
 need(oracle.evaluate(bad,dict(fs=x*x,fa=a,fb=b,fc=c))['N'].t!=want.t,'actual norm sign mutation rejected')
 for n in('shift-parent-check.json','shift-parent-check-optimized.json'):
  p=load(HERE/'source'/n);need(p['status']=='PASS'and p['equation_sha256']==PARENT_SHA,'parent complete receipt')
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,operations=102,
  operation_breakdown=counts,exact_degree=388,syntactic_degree=440,all_parent103_child102_rows_accounted=True,
  universal_shiftedI_L_W_carrier_inputmap=True,full_independent_octic_terms=35,
  centered_unique_leading='omega^4, degree388',actual_selected_coefficient='2^28*beta^224',
  actual_selected_monomial={'J':224,'w':40,'Y':76,'eta':40,'alpha':4,'F':4},
  actual_tuple_inputmap_controls=actual_controls,exact_free_signed_port_controls=free_controls,
  actual_tuple_degree_slices=slices,actual_inputcut_and_norm_mutations_rejected=True,
  whole_four_payloads=payloads,all_source_provenance_checked=True,ordinary_peer_pins_current_proof=True,equation_sha256=digest((HERE/'equation.json').read_bytes()),proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
  scope='Complete polynomial cuts/map and degreecertificate with authentic fixedtuple. Positivity and native/refutationexistence are the separate unbounded Ibound/shorttransport/canonicaln proof. No newLean/internal-ZFC certificate; canonicalpage unchanged.')
 target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
