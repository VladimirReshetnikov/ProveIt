#!/usr/bin/env python3
"""Independent bounded literal-source audit; does not call the author verify()."""
import argparse, collections, contextlib, hashlib, importlib, importlib.abc, importlib.util, io, json, math, random, subprocess, sys, zipfile
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions must be enabled')
PINS={'three_mass_unbounded_interface.py':'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a',
      'three_mass_unbounded_interface.json':'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
      'three_mass_unbounded_interface.md':'d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45'}
ARRIVAL='4e270aa4648c5fd7e18626507531046715976535'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
def sha(b):return hashlib.sha256(b if type(b)is bytes else b.encode()).hexdigest()
def req(ok,message):
 if not ok:raise ValueError(message)
def canon(v):return json.dumps(v,sort_keys=True,separators=(',',':'),allow_nan=False)
class Finder(importlib.abc.MetaPathFinder,importlib.abc.Loader):
 def __init__(self,root,pins):self.root=root;self.pins=pins;self.loaded={}
 def find_spec(self,name,path=None,target=None):
  if '.'not in name and (self.root/(name+'.py')).exists():
   req(name+'.py'in self.pins,'Unexpected local dependency');return importlib.util.spec_from_loader(name,self)
 def create_module(self,spec):return None
 def exec_module(self,module):
  p=self.root/(module.__name__+'.py');b=p.read_bytes();req(sha(b)==self.pins[p.name],'Dependency pin')
  self.loaded[p.name]=sha(b);module.__file__=str(p);exec(compile(b,str(p),'exec'),module.__dict__)
@contextlib.contextmanager
def parent(root,pins):
 stems={p.stem for p in root.glob('*.py')};prior={k:v for k,v in sys.modules.items() if k in stems};finder=Finder(root,pins)
 for k in prior:del sys.modules[k]
 sys.meta_path.insert(0,finder)
 try:yield importlib.import_module('residue_affine_packed_history'),finder
 finally:
  sys.meta_path.remove(finder)
  for k in list(sys.modules):
   if k in stems:del sys.modules[k]
  sys.modules.update(prior)
def node(op,a,b):
 if op in ('+','*'):a,b=sorted((a,b))
 return sha(canon([op,a,b]))
def atom(x):return sha(canon(['atom',x]))
def hashes(rows,inputs,overrides=None):
 e={n:atom(n) for n in inputs};e.update(overrides or {})
 for n,op,a,b in rows:
  if n in (overrides or {}):continue
  at=lambda x:e[x] if type(x)is str else atom(x)
  e[n]=node(op,at(a),at(b))
 return e
def execute(rows,values,mod=None):
 e=dict(values)
 for n,op,a,b in rows:
  x=e[a] if type(a)is str else a;y=e[b] if type(b)is str else b
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
  if mod:e[n]%=mod
 return e
def linear(rows,out,atoms):
 nodes={n:(op,a,b) for n,op,a,b in rows};memo={n:{n:1} for n in atoms}
 def f(x):
  if type(x)is int:return {'':x} if x else {}
  if x in memo:return memo[x]
  op,a,b=nodes[x];a=f(a);b=f(b)
  if op=='*':
   if set(a)<=set(['']):a,b=b,a
   req(set(b)<=set(['']),'Nonlinear clock word');r={k:v*b.get('',0) for k,v in a.items()}
  else:
   r=dict(a)
   for k,v in b.items():r[k]=r.get(k,0)+(v if op=='+' else -v)
  memo[x]={k:v for k,v in r.items() if v};return memo[x]
 return f(out)
def step(spec,state,N):
 if state=='h':return None
 applicable=[]
 for src,dst,op,counter in spec['instructions']:
  if src!=state:continue
  p=[2,3][counter]
  if op in ('dec','positive') and N%p:continue
  if op=='zero' and N%p==0:continue
  new=N*p if op=='inc' else N//p if op=='dec' else N
  tau=(108*N+96*new if op=='inc' else 96*N+108*new if op=='dec' else 192*N)+8
  applicable.append((dst,new,tau))
 req(len(applicable)<=1,'Nondeterministic fixture');return applicable[0] if applicable else None

def verify(repo,source_root):
 root=Path(repo)/WIP;sr=Path(source_root)
 for name,pin in PINS.items():req(sha((sr/name).read_bytes())==pin,'Author artifact pin')
 receipt=json.loads((sr/'three_mass_unbounded_interface.json').read_text());counts=collections.Counter();report=[]
 for name,pin in receipt['pins'].items():req(sha((root/name).read_bytes())==pin,'Initial source pin')
 for name,pin in receipt['executed_local_sources'].items():req(sha((root/name).read_bytes())==pin,'Executed source pin')
 # Pin the actual original core; this review reads its primitive formulas but does not execute it.
 data=subprocess.check_output(['git','-C',str(repo),'show',ARRIVAL+':docs/incoming/Three_Mass_Reversible_Computation.zip'],timeout=300)
 req(sha(data)==receipt['original_archives']['Three_Mass_Reversible_Computation.zip'],'Archive pin')
 with zipfile.ZipFile(io.BytesIO(data)) as z:
  core=z.read('three-mass-release/code/certificate.py')
 req(sha(core)=='fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8','Original core pin')
 with parent(root,receipt['executed_local_sources']) as (H,loader):
  for f in receipt['fixtures']:
   rows=f['source'];mapping=f['mapping'];m=mapping['modulus'];K=mapping['K'];table=tuple(tuple(r) for r in mapping['table'])
   old=H.build(table,form='raw',baseline=min(a for a,d in table));h=old['interfaces']['h'];B=old['interfaces']['B']
   inputs=f['parameters']+f['auxiliaries'];known=set(inputs);degrees={n:1 for n in inputs};nodes={};ops=collections.Counter()
   for n,op,a,b in rows:
    req(type(n)is str and n not in known and op in ('+','-','*'),'Typed DAG')
    req(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Closed DAG')
    da=degrees[a] if type(a)is str else 0;db=degrees[b] if type(b)is str else 0
    degrees[n]=da+db if op=='*' else max(da,db);known.add(n);nodes[n]=(op,a,b);ops['M' if op=='*' else 'A']+=1
   live=set();stack=[f['output']]
   while stack:
    n=stack.pop()
    if type(n)is str and n in live:continue
    if type(n)is str and n in nodes:live.add(n);stack.extend(nodes[n][1:])
   req(live==set(nodes),'Live full circuit')
   actual=dict(A=ops['A'],M=ops['M'],degree_upper_bound=degrees[f['output']],equations=len(f['comparisons']),exact_degree_claimed=False,positive_witnesses=len(f['auxiliaries']),total=len(rows))
   req(actual==f['ledger'],'Independent full ledger');counts['full_ledgers']+=1;counts['paid_gates']+=len(rows)
   req(len(f['comparisons'])==20 and f['comparisons'][-1]==['final_positive','y'],'Endpoint/domain row')
   env=hashes(rows,inputs)
   def at(x):return env[x] if type(x)is str else atom(x)
   squares=[node('*',node('-',at(a),at(b)),node('-',at(a),at(b))) for a,b in f['comparisons']]
   want=squares[0]
   for term in squares[1:]:want=node('+',want,term)
   req(env[f['output']]==want,'Complete SOS reconstruction');counts['complete_SOS_DAG_identities']+=1
   # Only h and B change from the inherited complete certificate; prove every other row under explicit cuts.
   cut={h:atom('@height'),B:atom('@radix')};new=hashes(rows,inputs,cut)
   cut_old=dict(cut,input=new['bridge_input'],target=new['bridge_target'])
   previous=hashes(old['source'],old['parameters']+old['auxiliaries'],cut_old)
   for n,_,_,_ in old['source']:
    req(previous[n]==new[n],'Unchanged inherited gate under height/radix cuts');counts['inherited_gate_identities']+=1
   for (a,b),(c,d) in zip(old['comparisons'],f['comparisons'][:18]):
    before=lambda x:previous[x] if type(x)is str else atom(x)
    after=lambda x:new[x] if type(x)is str else atom(x)
    req((before(a),before(b))==(after(c),after(d)),'Inherited comparison preserved');counts['inherited_comparisons']+=1
   req(linear(rows,h,inputs)=={'x':K,'':mapping['initial']+mapping['halt']-K,'final_positive':K,'height_slack':1,'T':1},'Charged positive height')
   bop,C,hsq=nodes[B];req(bop=='*' and type(C)is int and C>=max(old['radix_multiplier'],2384*m+2) and C&(C-1)==0,'Paid safe dyadic coefficient')
   req(nodes[hsq]==('*',h,h),'Literal paid height square')
   req(nodes['bridge_input']==('+','bridge_input_scaled',mapping['initial']) and nodes['bridge_input_scaled']==('*',K,'x'),'Paid raw loader')
   # The actual clock word is affine in the already paid hats; reconstruct every coefficient independently.
   clk=f['comparisons'][-2][0]
   byslope={a:c for (a,d),(c,b) in zip(table,mapping['clocks'])};base=byslope[old['baseline']]
   expected={'quotient_hat':base,'':-base}
   for i,a in enumerate(old['classes']):expected[f'product{i}_hat']=byslope[a]-base;expected['']-=byslope[a]-base
   for i,(c,b) in enumerate(mapping['clocks']):expected[f'edge{i}_hat']=b;expected['']-=b
   expected={k:v for k,v in expected.items() if v}
   req(linear(rows,clk,list(expected.keys()-{''}))==expected,'Entire clock word coefficient identity');counts['clock_affine_identities']+=1
   # Independently replay residue rows on positive values and artificial trap states.
   codes=mapping['codes'];states={v:k for k,v in codes.items()}
   for n in range(1,40*m+1):
    payload,q=divmod(n-1,K);payload+=1;q+=1
    hit=step(f['machine'],states.get(q),payload) if q in states else None
    if hit:dest,out,tau=codes[hit[0]],hit[1],hit[2]
    else:dest,out,tau=mapping['trap'],payload,192*payload+8
    z,r=divmod(n-1,m);a,d=table[r];c,b=mapping['clocks'][r]
    req((a*z+d,c*z+b)==(K*(out-1)+dest,tau),'Literal totalized state/clock');counts['residue_state_clock_cases']+=1
   rng=random.Random(431+m+len(rows))
   for i in range(16):
    vals={n:rng.randrange(-2,4) for n in inputs};e=execute(rows,vals,1000003)
    ev=lambda v:e[v] if type(v)is str else v
    req(e[f['output']]==sum((ev(a)-ev(b))**2 for a,b in f['comparisons'])%1000003,'Independent complete modular output');counts['modular_full_outputs']+=1
   for v in f['outer_histories']:
    state='s';N=v['x']+1;ticks=[];seen=set();ns=[]
    while state!='h':
     number=K*(N-1)+codes[state];req(number not in seen,'Repeated accepted state');seen.add(number);ns.append(number)
     hit=step(f['machine'],state,N);req(hit is not None,'Actual halt path');state,N,tau=hit;ticks.append(tau)
    height=v['h'];radix=v['radix']
    req((N,sum(ticks),len(ticks))==(v['y'],v['T'],v['steps']),'Exact saved first-halt clock')
    req(all(n<=m*height for n in ns) and len(ticks)<=m*height,'Distinct-state duration bound')
    req(all(0<t<=2384*height for t in ticks) and sum(ticks)<=2384*m*height**2<radix-1,'Strict no-wrap bound')
    word=sum(t*radix**i for i,t in enumerate(ticks))
    req(word==(radix-1)*(v['clock_quotient_hat']-1)+v['T'],'Actual clock quotient')
    counts['exact_clock_no_wrap_fixtures']+=1
   # Whole halting traces agree under coprime scaling; clocks obey the exact nonconstant scaling law.
   for N in range(1,25):
    for cofactor in (5,7,11):
     for state in f['machine']['states']:
      a=step(f['machine'],state,N);b=step(f['machine'],state,cofactor*N)
      req((a is None)==(b is None),'Valuation guard invariant')
      if a:req((b[0],b[1],b[2]-8)==(a[0],cofactor*a[1],cofactor*(a[2]-8)),'Cofactor transition/clock identity')
      counts['coprime_transition_cases']+=1
   report.append(dict(name=f['name'],ledger=actual,clock_radix_multiplier=C))
  loaded=dict(loader.loaded)
 return dict(status='PASS_BOUNDED_INDEPENDENT_REVIEW',author_pins=PINS,original_core_sha256=sha(core),checks=dict(sorted(counts.items())),circuits=report,executed_parent_pins=loaded,
             scope='General proof read; independent literal source and bounded evidence; cold author CLI only; no materialized native Pell zero or universal-input claim',reviewer_sha256=sha(Path(__file__).read_bytes()))
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--source-root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args()
 r=verify(a.repo,a.source_root)
 if a.expect:req(canon(r)==canon(json.loads(a.expect.read_text())),'Receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'checks':r['checks']},sort_keys=True))
if __name__=='__main__':main()
