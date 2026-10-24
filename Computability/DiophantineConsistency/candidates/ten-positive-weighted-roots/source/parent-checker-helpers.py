#!/usr/bin/env python3
"""Independent full affine-prefix map, octic norm, tuple and parity controls."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from math import gcd
from pathlib import Path
import random
import sys

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'candidates/ten-positive-quadratic-projection-shared'
PAGE=ROOT/'candidates/one-page-scaled10'
PARENT_SHA='507cb56d69f0af5f678bc2984f1b5061d21751581543679ee99c8d9111fe0045'

def need(ok,message):
 if not ok:raise ValueError(message)
def digest(x):return sha256(x).hexdigest()
def load(p):return json.loads(p.read_bytes())

def evaluate(rows,inputs,p=None):
 env=dict(inputs)
 for name,op,a,b in rows:
  u=a if type(a)is int else env[a];v=b if type(b)is int else env[b]
  val=u+v if op=='+'else u-v if op=='-'else u*v
  env[name]=val if p is None else val%p
 return env

def verify_map(parent,child,mapping):
 old,rows=parent['source'],child['source']
 need(old[:2]==[['2j','*',2,'j'],['J','+','2j',1]],'complete two affine gates')
 need(rows==old[2:],'all103 literal rows unchanged with every operand')
 need(mapping['deleted_rows']==[dict(parent_index=i,row=old[i])for i in range(2)],'both parent affine gates accounted')
 need(mapping['retained_rows']==[dict(parent_index=i,child_index=i-2,register=r[0])for i,r in enumerate(old)if i>=2],
      'every105 parent and103 child gate accounted')
 need(child['witnesses']==['J']+parent['witnesses'][1:]and
      all('j'not in r[2:]and'2j'not in r[2:]for r in rows),'exact input replacement and no other removed-name uses')
 need(child['fixed_numerals']==parent['fixed_numerals']==['beta','K0','MC','MF']and
      child['output']==parent['output']=='N','complete tuple and output retained')

def line_degree(values,p):
 degree=-1;level=0;values=list(values)
 while values:
  if values[0]:degree=level
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return degree

def pell(A,n):
 x,y,u,v=1,0,A,1;D=A*A-1;sign=1 if n>=0 else-1;n=abs(n)
 while n:
  if n&1:x,y=x*u+D*y*v,x*v+y*u
  u,v=u*u+D*v*v,2*u*v;n//=2
 return x,sign*y

def main():
 raw=(HERE/'source/parent-equation.json').read_bytes();need(digest(raw)==PARENT_SHA,'entire105 parent')
 parent=json.loads(raw);child=load(HERE/'equation.json');remap=load(HERE/'PREFIX_REMAP.json')
 verify_map(parent,child,remap)
 need(child['domain']=='strictly positive integers'and len(child['witnesses'])==10,'exact strictly positive ten-variable domain')
 for name,pin in load(PARENT/'MANIFEST.json')['files'].items():need(digest((PARENT/name).read_bytes())==pin,'complete frozen parent seal '+name)
 provenance=load(HERE/'PROVENANCE.json')
 for name,pin in provenance['dependencies'].items():
  data=(HERE/name).read_bytes();need(data==(ROOT/pin['repository_path']).read_bytes()and digest(data)==pin['sha256'],'whole pinned dependency '+name)
 for name,pin in load(HERE/'BUILD.json')['sha256'].items():need(digest((HERE/name).read_bytes())==pin,'generated seal '+name)
 rows=child['source'];known=set(child['witnesses']+child['fixed_numerals']);degrees={v:1 for v in child['witnesses']}|{v:0 for v in child['fixed_numerals']};deps={}
 for name,op,a,b in rows:
  need(name not in known and op in('+','-','*')and all(type(x)is int or x in known for x in(a,b)),'acyclic fresh gate')
  da,db=(0 if type(x)is int else degrees[x]for x in(a,b))
  degrees[name]=da+db if op=='*'else max(da,db);known.add(name);deps[name]=(a,b)
 live=set();todo=['N']
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  live.add(v);todo.extend(deps.get(v,()))
 need(live==known,'all103 gates,10 inputs and4 ports live')
 counts=dict(Counter(r[1]for r in rows))
 need(len(rows)==child['operations']==103 and counts==child['operation_breakdown']=={'*':60,'+':25,'-':18},'actual103-operation complete graph')
 need(degrees['N']==child['syntactic_degree']==464 and child['exact_degree']==408,'degree contracts')
 for name,d in child['register_degrees'].items():need(degrees[name]==d,'every front degree bound')
 helper=HERE/'source/independent_norm_oracle.py';need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent oracle')
 spec=importlib.util.spec_from_file_location('freeJ_positive10_oracle',helper);oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 x,a,b,c,_,omega=[oracle.variable(i)for i in range(6)]
 tail=rows[90:];need(len(tail)==13 and tail==parent['source'][92:],'whole unchanged13-gate norm tail')
 want=oracle.norm_oracle(x,[a,b,c]);have=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=c))['N']
 need(want.t==have.t and len(want.t)==35,'all35 independent octic norm coefficients')
 centered=oracle.evaluate(tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N']
 weights=(58,78,84,0,0,102);d=max(sum(k*w for k,w in zip(m,weights))for m in centered.t)
 top={m:v for m,v in centered.t.items()if sum(k*w for k,w in zip(m,weights))==d}
 need(d==408 and top=={(0,0,0,0,0,4):1},'unique centered leadingomega4 at degree408')
 coefficients={};payloads={};binding=load(HERE/'coefficients/BINDING.json')
 need(binding==child['coefficient_binding']==parent['coefficient_binding'],'whole original compact44 binding unchanged')
 for name,pin in binding['ports'].items():
  blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
  need(digest(blob)==pin['gzip_sha256']and digest(raw)==pin['raw_sha256'],'whole authentic tuple port '+name)
  coefficients[name]=int.from_bytes(raw,'little');need(coefficients[name].bit_length()==pin['bits'],'whole port width')
  payloads[name]=dict(raw_sha256=digest(raw),bits=pin['bits'])
 beta=coefficients['beta'];need(beta==2**590069-1 and beta%2==1 and beta>=31 and
  0<coefficients['MC']<beta<coefficients['MF']<2*beta and coefficients['K0']>0,'closed actual tuple meets strengthenedbox')
 bfs={}
 for name,filename in [('beta','beta.bin.gz'),('K0','K.bin.gz'),('MC','MC.bin.gz'),('MF','MF_source.bin.gz')]:
  blob=(PAGE/'coefficients'/filename).read_bytes()
  need(digest(blob)==load(HERE/'source/BFS_SOURCE_PINS.json')['copied_files']['coefficients/'+filename],'whole pinned BFS coefficient bytes '+name)
  raw=gzip.decompress(blob);bfs[name]=int.from_bytes(raw,'little')
 need(all(bfs[k]==coefficients[k]for k in('beta','MC','MF'))and bfs['K0']!=coefficients['K0']and bfs['K0']>0,'wholeBFS arithmetic box and honestK distinction')
 need(load(HERE/'source/BFS_TUPLE_VERIFY.json')['status']=='PASS'and
      load(HERE/'source/BFS_TUPLE_VERIFY.json')['all_four_page_payloads_raw_byte_identical'],'retained completeBFS native binding receipt')
 source=(HERE/'source/SOURCE61.tex').read_text();block=source.split('\\label{thm:source}',1)[1].split('\\end{theorem}',1)[0]
 need('a strictly positive solution'in block and'J>1'not in block and'J>1'in source,'actual soundness theorem vs canonicalpromise sourcepin')
 rng=random.Random(103408);actual=free=0
 for prime in(1009,(1<<127)-1):
  ports={k:v%prime for k,v in coefficients.items()}
  for j in range(60):
   inputs={v:rng.randrange(-20,21)for v in child['witnesses']};inputs['J']=1+j%8;inputs.update(ports)
   oldinputs={k:v for k,v in inputs.items()if k!='J'};oldinputs['j']=(inputs['J']-1)*pow(2,-1,prime)%prime
   before=evaluate(parent['source'],oldinputs,prime);after=evaluate(rows,inputs,prime)
   need(before['J']==after['J']and all(before[r[0]]==after[r[0]]for r in rows),'whole affine map includesJ1/evenJ controls')
   actual+=1
 for _ in range(50):
  inputs={v:rng.randrange(-3,4)for v in parent['witnesses']+parent['fixed_numerals']}
  childinputs={k:v for k,v in inputs.items()if k!='j'};childinputs['J']=2*inputs['j']+1
  before=evaluate(parent['source'],inputs);after=evaluate(rows,childinputs)
  need(all(before[r[0]]==after[r[0]]for r in rows),'exact signed free-port affine identity')
  free+=1
 slices=[]
 for prime in((1<<127)-1,(1<<89)-1):
  ports={k:v%prime for k,v in coefficients.items()};base={v:rng.randrange(1,prime)for v in child['witnesses']};direction={v:rng.randrange(1,prime)for v in child['witnesses']}
  vals=[evaluate(rows,ports|{v:(base[v]+t*direction[v])%prime for v in child['witnesses']},prime)['N']for t in range(466)]
  need(line_degree(vals,prime)==408,'actual tuple line attainsdegree408')
  slices.append(dict(prime_bits=prime.bit_length(),degree=408))
 folds=0
 for A in range(3,9):
  for m in range(1,7):
   f,I=pell(A,m)
   for nu in range(-4*m+1,4*m,2):
    q,t=divmod(nu,2*m);p=min(t,2*m-t);sgn=-1 if q%2 else 1
    need(p%2==1 and(pell(A,nu)[1]-sgn*pell(A,p)[1])%f==0,'signed fold preserves oddness before qparity')
    folds+=1
 # F2 exhaustive polynomial implication; the written proof is unbounded.
 for J in range(2):
  q=(J+1)%2
  if q==1:
   need(J==0,'odd q forces evenJ')
   for G in range(2):
    for MC in range(2):
     for MF in range(2):need((G*(q*q-1)+(MC+q*MF)*J)%2==0,'oddq forces evenR for any mask parity')
 bad=deepcopy(child);bad['source'][0][1]='+'
 try:verify_map(parent,bad,remap)
 except ValueError:pass
 else:raise ValueError('actual prefix mutation accepted')
 bad=deepcopy(tail);bad[-1][1]='+'
 need(oracle.evaluate(bad,dict(fs=x*x,fa=a,fb=b,fc=c))['N'].t!=want.t,'actual norm sign mutation rejected')
 for name in('parent-check.json','parent-check-optimized.json'):
  r=load(HERE/'source'/name);need(r['status']=='PASS'and r['exact_degree']==408 and r['equation_sha256']==PARENT_SHA,'full frozen parent degree andnorm receipt')
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,operations=103,
  operation_breakdown=counts,exact_degree=408,syntactic_degree=464,all105_parent_rows_and103_child_rows_accounted=True,
  universal_polynomial_relation='P_old(j,rest)=P_new(2j+1,rest); invertible affine change overQ preserves exactdegree408.',
  full_independent_norm_terms=35,unique_centered_leading_term='omega^4',
  actual_tuple_affine_controls=actual,exact_free_signed_port_controls=free,actual_tuple_degree_slices=slices,
  odd_index_fold_controls=folds,F2_parity_implication_exhaustive=True,
  actual_prefix_and_norm_mutations_rejected=True,whole_four_fixed_ports=payloads,bfs_uniform_arithmetic_box=True,
  proof_sha256=digest((HERE/'PROOF.md').read_bytes()),equation_sha256=digest((HERE/'equation.json').read_bytes()),
  scope='Complete universal affine gate map, fullnorm and degree certificate with actual closedtuple. Enlarged positiveJ-domain is licensed by the separate unbounded parity/deferred-coprimality/source61proof, includingJ1. No newLean/internal-ZFC derivation; canonicalpage unchanged.')
 target='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json';(HERE/target).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
