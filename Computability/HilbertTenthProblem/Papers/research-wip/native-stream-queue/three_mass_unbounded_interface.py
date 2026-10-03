#!/usr/bin/env python3
"""Bounded, source-pinned research bridge; no universal numeric instance claimed."""
import argparse, copy, hashlib, importlib, importlib.abc, importlib.util, json, math, random, sys
from collections import Counter
from pathlib import Path
if not __debug__: raise RuntimeError('Historical dependencies require assertions enabled')
PINS={'three_mass_arithmetic.py':'d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0',
 'residue_affine_packed_history.py':'d06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4',
 'residue_affine_sparse_universal.py':'0d7c14166774d2e897bf90712ff2cba28516abfe59a959770afaa78d35632d3b',
 'residue_affine_sparse_factored.py':'060757ef9bb6e6d1f9ae3bd85ca0ace91a35d92cd4f77662100be7c529772b13'}
def sha(b):return hashlib.sha256(b).hexdigest()
def need(x,s):
 if not x:raise ValueError(s)
def exact(a,b):
 return type(a)is type(b) and (a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a) if type(a)is dict else len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b)) if type(a)is list else a==b)
class SourceFinder(importlib.abc.MetaPathFinder,importlib.abc.Loader):
 def __init__(self,root):self.root=root;self.loaded={}
 def find_spec(self,fullname,path=None,target=None):
  if '.'not in fullname and (self.root/(fullname+'.py')).is_file():return importlib.util.spec_from_loader(fullname,self,origin=str(self.root/(fullname+'.py')))
 def create_module(self,spec):return None
 def exec_module(self,module):
  p=self.root/(module.__name__+'.py');b=p.read_bytes();self.loaded[p.name]=sha(b);module.__file__=str(p);exec(compile(b,str(p),'exec'),module.__dict__)
def run_source(machine,state,N):
 if state==machine.halt:return None
 hits=[]
 for ins in machine.instructions:
  if ins.source!=state:continue
  p=(2,3)[ins.counter];op=ins.operation
  if op in ('dec','positive') and N%p:continue
  if op=='zero' and N%p==0:continue
  new=N*p if op=='inc' else N//p if op=='dec' else N
  tick=(108*N+96*new if op=='inc' else 96*N+108*new if op=='dec' else 192*N)+8
  hits.append((ins.target,new,tick,op,p))
 need(len(hits)<=1,'Deterministic source');return hits[0] if hits else None

def residue_map(machine,initial):
 machine.validate();need(initial in machine.states and initial!=machine.halt,'Prototype nonempty initial state')
 codes={q:i+1 for i,q in enumerate(machine.states)};trap=len(codes)+1;K=trap
 while math.gcd(K,6)!=1:K+=1
 modulus=6*K
 def numeric(n):
  N,q=divmod(n-1,K);N+=1;q+=1
  name=machine.states[q-1] if q<=len(machine.states) else None
  hit=run_source(machine,name,N) if name is not None else None
  if hit is None:dest,out,tick,op,p=trap,N,192*N+8,'nop',2
  else:dest,out,tick,op,p=codes[hit[0]],*hit[1:]
  return K*(out-1)+dest,tick,op,p
 table=[];clocks=[]
 for s in range(1,modulus+1):
  d,tau,op,p=numeric(s)
  a=modulus*p if op=='inc' else modulus//p if op=='dec' else modulus
  c=6*(108+96*p) if op=='inc' else 6*96+6*108//p if op=='dec' else 6*192
  table.append((a,d));clocks.append((c,tau))
 byslope={}
 for (a,d),(c,b) in zip(table,clocks):
  need(a not in byslope or byslope[a]==c,'Existing slope classes suffice for clock');byslope[a]=c
 return dict(K=K,modulus=modulus,codes=codes,trap=trap,initial=codes[initial],halt=codes[machine.halt],table=table,clocks=clocks,clock_slope=byslope),numeric

def evaluate(source,values):
 e=dict(values)
 def at(v):return e[v] if type(v)is str else v
 for n,op,a,b in source:
  need(n not in e,'Fresh gate');x,y=at(a),at(b);e[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return e

def ledger(source,out,parameters,aux):
 known=set(parameters+aux);degrees={n:1 for n in known};nodes={};counts=Counter()
 for n,op,a,b in source:
  need(n not in known and op in ('+','-','*'),'Valid DAG row')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Closed DAG')
  da=degrees[a] if type(a)is str else 0;db=degrees[b] if type(b)is str else 0
  degrees[n]=da+db if op=='*' else max(da,db);known.add(n);nodes[n]=(a,b);counts['M' if op=='*' else 'A']+=1
 seen=set();todo=[out]
 while todo:
  n=todo.pop()
  if type(n)is str and n in nodes and n not in seen:seen.add(n);todo.extend(nodes[n])
 need(seen==set(nodes),'Every emitted gate is live')
 return dict(total=len(source),M=counts['M'],A=counts['A'],positive_witnesses=len(aux),degree_upper_bound=degrees[out],exact_degree_claimed=False)

def build(H,mapping):
 table=mapping['table'];old=H.build(table,form='raw',baseline=min(a for a,d in table));p=copy.deepcopy(old)
 # Explicit ports preserve original natural x,y,T and positive native auxiliaries.
 pre=[('bridge_input_scaled','*',mapping['K'],'x'),('bridge_input','+', 'bridge_input_scaled',mapping['initial']),
      ('bridge_final_minus_one','-','final_positive',1),('bridge_final_scaled','*',mapping['K'],'bridge_final_minus_one'),
      ('bridge_target','+','bridge_final_scaled',mapping['halt'])]
 rename=lambda v:'bridge_input' if v=='input' else 'bridge_target' if v=='target' else v
 C=1
 req=max(old['radix_multiplier'],2384*mapping['modulus']+2)
 while C<req:C*=2
 h=old['interfaces']['h'];B=old['interfaces']['B'];rows=list(pre)
 for n,op,a,b in old['source']:
  if n==h:
   rows += [('bridge_height_without_time',op,rename(a),rename(b)),(n,'+','bridge_height_without_time','T')]
  elif n==B:rows += [('bridge_height_square','*',h,h),(n,'*',C,'bridge_height_square')]
  else:rows.append((n,op,rename(a),rename(b)))
 cache={(op,*sorted((a,b),key=repr)) if op in ('+','*') else (op,a,b):n for n,op,a,b in rows}
 def emit(op,a,b):
  if op=='+' and (a==0 or b==0):return b if a==0 else a
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and (a==1 or b==1):return b if a==1 else a
  key=(op,*sorted((a,b),key=repr)) if op in ('+','*') else (op,a,b)
  if key not in cache:
   name='bridge_'+str(len(rows));cache[key]=name;rows.append((name,op,a,b))
  return cache[key]
 def add(xs):
  z=0
  for x in xs:z=emit('+',z,x)
  return z
 # Share the already emitted selected quotient fields. No new native lane.
 W=old['interfaces']['W'];base=mapping['clock_slope'][old['baseline']]
 terms=[emit('*',base,W)]
 unhat={a:n for n,op,a,b in rows if op=='-' and b==1 and type(a)is str}
 for i,slope in enumerate(old['classes']):terms.append(emit('*',mapping['clock_slope'][slope]-base,unhat[f'product{i}_hat']))
 groups={}
 for i,(_,d) in enumerate(mapping['clocks']):groups.setdefault(d,[]).append(unhat[f'edge{i}_hat'])
 terms += [emit('*',d,add(xs)) for d,xs in sorted(groups.items())]
 tickword=add(terms)
 Bm=next(n for n,op,a,b in rows if op=='-' and a==B and b==1)
 clock_rhs=emit('+',emit('*',Bm,emit('-','clock_quotient_hat',1)),'T')
 pairs=[(rename(a),rename(b)) for a,b in old['comparisons']]+[(tickword,clock_rhs),('final_positive','y')]
 p=dict(source=rows,comparisons=pairs,parameters=['x','y','T'],auxiliaries=old['auxiliaries']+['final_positive','clock_quotient_hat'],
        interfaces=dict(old['interfaces'],input='bridge_input',target='bridge_target',clock_word=tickword,clock_rhs=clock_rhs),
        radix_multiplier=C,mapping=mapping,baseline=old['baseline'],classes=old['classes'],domain='x,y,T natural; all auxiliaries positive')
 p['polynomial_source'],p['output']=H.native_host.polynomial_source(p)
 p['ledger']=ledger(p['polynomial_source'],p['output'],p['parameters'],p['auxiliaries'])
 p['ledger']['equations']=len(pairs)
 return p,old

def pack_outer(packet,path,ticks):
 # path is the exact encoded first-halt sequence, never a microscopic CA trace.
 m=packet['mapping']['modulus'];K=packet['mapping']['K'];T=sum(ticks);x=(path[0]-packet['mapping']['initial'])//K;y=(path[-1]-packet['mapping']['halt'])//K+1
 qs,rs=zip(*(divmod(n-1,m) for n in path[:-1]));h=1
 while h<=max([path[0]+path[-1]+T]+list(qs)):h*=2
 B=packet['radix_multiplier']*h*h;duration=len(ticks);P=B**duration;J=(P-1)//(B-1)
 pack=lambda xs:sum(v*B**i for i,v in enumerate(xs))
 W=pack(qs);E=[pack([int(r==i) for r in rs]) for i in range(m)]
 Z=[pack([q if packet['mapping']['table'][r][0]==a else 0 for q,r in zip(qs,rs)]) for a in packet['classes']]
 word=pack(ticks);need((word-T)%(B-1)==0 and word>=T,'Clock quotient')
 v=dict(x=x,y=y,T=T,final_positive=y,height_slack=h-path[0]-path[-1]-T,global_slack=P-J-W-1-sum(Z)-len(Z),quotient_hat=W+1,clock_quotient_hat=1+(word-T)//(B-1))
 v.update({f'edge{i}_hat':e+1 for i,e in enumerate(E)});v.update({f'product{i}_hat':z+1 for i,z in enumerate(Z)})
 need(all(v[n]>0 for n in packet['auxiliaries'] if not n.startswith('native__')),'All outer positive')
 env=evaluate([row for row in packet['source'] if not row[0].startswith('native__')],v)
 def at(n):return env[n] if type(n)is str else n
 need(all(at(a)==at(b) for a,b in packet['comparisons'][:2]+packet['comparisons'][-2:]),'Complete outer equalities')
 need(at(packet['interfaces']['joined_H']) & at(packet['interfaces']['joined_M'])==at(packet['interfaces']['joined_Z']),'Actual full joined AND')
 need(duration<=m*h and T<B-1,'Clock no-wrap bounds')
 return dict(x=x,y=y,T=T,steps=duration,h=h,radix=B,clock_quotient_hat=v['clock_quotient_hat'],native_witnesses_materialized=False)

def verify(repo):
 root=Path(repo).resolve()/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
 for f,pin in PINS.items():need(sha((root/f).read_bytes())==pin,'Pinned '+f)
 finder=SourceFinder(root);sys.meta_path.insert(0,finder)
 try:
  S=importlib.import_module('three_mass_arithmetic');H=importlib.import_module('residue_affine_packed_history')
  sources,archives=S.source_bytes(repo)
  counts=Counter();fixtures=[];rng=random.Random(20261002)
  with S.subjects(sources) as (C,CT):
   specs=[('incdec',('s','a','h'),('s','a','inc',0),('a','h','dec',0)),
          ('zero3',('s','h'),('s','h','zero',1)),('nop',('s','h'),('s','h','nop',0)),
          ('positive3',('s','h'),('s','h','positive',1))]
   for name,states,*instr in specs:
    machine=C.Machine(states,'h',tuple(C.Instruction(*v) for v in instr)).validate();mapping,numeric=residue_map(machine,'s');packet,parent=build(H,mapping)
    for s in range(1,mapping['modulus']+1):
     a,d=mapping['table'][s-1];c,b=mapping['clocks'][s-1]
     for q in range(25):
      nxt,tick,*_=numeric(mapping['modulus']*q+s);need((nxt,tick)==(a*q+d,c*q+b),'Exact residue and clock affine rows');counts['residue_clock_rows']+=1
    # All original primitive branch forms, including the clock, are matched independently.
    for branch in machine.branches():
     f=C.branch_forms(branch,{'e':1},{'u':1})
     for v in range(1,25):
      es={'e':1,'u':v-1};N,new,tick=[C.evaluate_affine(a,es) for a in f];hit=run_source(machine,branch.source,N)
      need(hit[:3]==(branch.target,new,tick),'Literal source transition+clock');counts['literal_branch_rows']+=1
    outer=[]
    for x in range(24):
     state='s';N=x+1;path=[mapping['K']*(N-1)+mapping['initial']];ticks=[]
     for j in range(12):
      hit=run_source(machine,state,N)
      if hit is None:break
      state,N,tick,*_=hit;ticks.append(tick);path.append(mapping['K']*(N-1)+mapping['codes'][state])
      if state==machine.halt:break
     if state==machine.halt:
      outer.append(pack_outer(packet,path,ticks));counts['outer_full_AND_histories']+=1
    # Execute every complete native gate on arbitrary signed values; verify full literal SOS.
    for i in range(12):
     v={k:rng.randrange(-2,4) for k in packet['parameters']+packet['auxiliaries']};e=evaluate(packet['polynomial_source'],v)
     at=lambda z:e[z] if type(z)is str else z
     need(e[packet['output']]==sum((at(a)-at(b))**2 for a,b in packet['comparisons']),'Full emitted polynomial equals every paid squared row');counts['full_signed_SOS']+=1
     ep=evaluate(parent['source'],dict(v,input=e['bridge_input'],target=e['bridge_target'],height_slack=v['height_slack']+v['T']))
     # New B is genuinely changed; no parent polynomial equality is claimed.
     need(e[packet['interfaces']['h']]==ep[parent['interfaces']['h']],'Charged height interface identity');counts['height_bridge_identities']+=1
    fixtures.append(dict(name=name,machine={'states':list(states),'instructions':[list(i) for i in instr]},mapping=mapping,
                         ledger=packet['ledger'],source=packet['polynomial_source'],output=packet['output'],parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],comparisons=packet['comparisons'],outer_histories=outer))
   # Raw acceptance cannot distinguish multiplicative cofactors coprime to6.
   for a in range(4):
    for b in range(4):
     for c in (1,5,7,11,13):
      N=2**a*3**b*c
      need((N%2==0)==(a>0) and (N%3==0)==(b>0),'Cofactor guard invariant');counts['cofactor_examples']+=1
  return dict(format='three-mass-unbounded-interface-scout-v1',pins=PINS,executed_local_sources=dict(sorted(finder.loaded.items())),original_archives=archives,
              counts=dict(counts),fixtures=fixtures,scope='Fixed finite source; natural raw x,y,T; unbounded native positive witnesses; no numerical universal source/ordinary counter loader claimed',
              proof_status='New clock bridge has accompanying mathematical argument; bounded checks are not native Pell witness materializations')
 finally:sys.meta_path.remove(finder)

def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=json.loads(json.dumps(verify(a.repo)))
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact saved receipt')
 if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','counts':out['counts'],'ledgers':{v['name']:v['ledger'] for v in out['fixtures']}},sort_keys=True))
if __name__=='__main__':main()
