#!/usr/bin/env python3
"""Four complete nonempty fixed-table projective sources from authenticated JSON.
Bounded standard-library CLI only. No historical module, builder, or suite runs.
The four graphs preserve the matrix query; only the first two preserve words.
"""
import argparse,copy,json,hashlib,itertools,random
from fractions import Fraction
from collections import Counter,deque
from pathlib import Path
PINS={'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c'}

PINS.update({'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_inverse_stallings_controller.py': 'f55cc2536854c2c3448558541dc35f1888b33ae941307798f02e78dd20ff6230', 'group_inverse_stallings_controller.json': '283ddbff12ef0e42be06ca2ab123a15cdbcdb4f02e5daa50571127549cb3db90', 'group_inverse_stallings_controller.md': '219917bda05e9bdbe460cab56a4768f67a6eb1da9ef816b06307df43039c6237'})
FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
P='controller__geometry_power'
R={1:1,2:'controller__lane_factor0',4:'controller__lane_repunit1',8:'controller__lane_repunit2'}
U=(1,5);RT=(2,3,6,7);BMAC=U*5;AMAC=RT+BMAC
inv=lambda w:tuple(l+1 if l%2 else l-1 for l in reversed(w))
CODES=(AMAC,BMAC,inv(AMAC),inv(BMAC))
NIELSEN=(RT,BMAC,inv(RT),inv(BMAC))
def need(c,m):
 if not c:raise ValueError(m)

def sha(b):return hashlib.sha256(b).hexdigest()

def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def separate(codes):
 need(all(all(type(l)is int and 1<=l<=8 for l in w)for w in codes),'physical macro alphabet')
 edges=[(0,0,0)];next_state=1
 for word in codes:
  state=0
  for i,label in enumerate(word):
   dest=0 if i==len(word)-1 else next_state
   if dest:next_state+=1
   edges.append((state,dest,label));state=dest
 return edges

def share(codes):
 need(all(all(type(l)is int and 1<=l<=8 for l in w)for w in codes),'physical macro alphabet')
 codes=sorted(set(tuple(w)for w in codes));proper={()}
 for word in codes:proper.update(word[:i]for i in range(1,len(word)))
 outgoing={p:set()for p in proper}
 for word in codes:
  for i,label in enumerate(word):outgoing[word[:i]].add((label,word[:i+1]if i<len(word)-1 else()))
 # The hub stays distinguished. Proper-prefix transitions strictly increase
 # prefix length; bottom-up identical labeled continuations are bisimilar.
 classes={():0};signatures={};representatives={}
 for p in sorted(proper-{()},key=lambda p:(-len(p),p)):
  sig=tuple(sorted((label,classes[q])for label,q in outgoing[p]))
  if sig not in signatures:signatures[sig]=len(signatures)+1;representatives[signatures[sig]]=sig
  classes[p]=signatures[sig]
 hub=tuple(sorted((label,classes[q])for label,q in outgoing[()]))
 raw={(0,0,0)}
 for label,q in hub:raw.add((0,q,label))
 for state,sig in representatives.items():
  for label,q in sig:raw.add((state,q,label))
 # Deterministic state relabeling puts most incidences at cheap numeral1.
 states=sorted(representatives,key=lambda s:(-sum(s in(a,b)for a,b,l in raw),s));rename={0:0,**{s:i+1 for i,s in enumerate(states)}}
 edges=sorted({(rename[a],rename[b],l)for a,b,l in raw},key=lambda e:(e!=(0,0,0),e))
 return edges,dict(proper_prefixes=[list(p)for p in sorted(proper)],prefix_class=[dict(prefix=list(p),state=rename[c])for p,c in sorted(classes.items())],class_continuations={str(rename[k]):[[l,rename[v]]for l,v in sig]for k,sig in representatives.items()},root_continuations=[[l,rename[v]]for l,v in hub])

def language_equivalence(left,right):
 def step(edges,S,label):return frozenset(b for a,b,l in edges if a in S and l==label)
 start=(frozenset({0}),frozenset({0}));seen={start};todo=deque([start])
 while todo:
  a,b=todo.popleft();need((0 in a)==(0 in b),'exact automaton accepting-state equivalence')
  for label in range(9):
   pair=step(left,a,label),step(right,b,label)
   if pair not in seen:seen.add(pair);todo.append(pair)
 return len(seen)

class Emitter:
 def __init__(self):self.rows=[];self.serial=0;self.memo={}
 def gate(self,op,a,b,name=None):
  if op=='+'and a==0:return b
  if op=='+'and b==0:return a
  if op=='-'and b==0:return a
  if op=='*'and(a==0 or b==0):return 0
  if op=='*'and a==1:return b
  if op=='*'and b==1:return a
  key=(op,tuple(sorted((a,b),key=repr))if op in('+','*')else(a,b))
  if key in self.memo:return self.memo[key]
  name=name or 'controller__flow_'+str(self.serial);self.serial+=1;self.rows.append([name,op,a,b]);self.memo[key]=name;return name
 def total(self,values):
  out=0
  for value in values:out=self.gate('+',out,value)
  return out

def execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def ledger(rows,free,roots):
 d={n:1 for n in free};defs={};M=0
 for n,o,a,b in rows:
  need(n not in d and o in('+','-','*'),'fresh gate');need(all(type(v)is int or type(v)is str and v in d for v in(a,b)),'closure')
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0;d[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);M+=o=='*'
 seen=set();used=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 need(seen==set(defs)and used==set(free),'full source liveness')
 return dict(operations=len(rows),M=M,A=len(rows)-M,degree_upper=max(d[n]if type(n)is str else 0 for n in roots))

class E(Emitter):
 def gate(self,op,a,b,name=None):
  if type(a)is int and type(b)is int:return a*b if op=='*'else a+b if op=='+'else a-b
  if op=='-'and a==b:return 0
  return super().gate(op,a,b,name)

def transform(T,edges,flow_mode='generic',positions=None,pack_mode='direct'):
 POW={0:1,1:P,2:'controller__lane_power1',4:'controller__lane_power2',8:'controller__lane_power3'}
 n=len(edges);m=8
 while m<n:m*=2
 reps=dict(R)
 hats=[f'controller__edge_hat{i+1}'for i in range(n)]; em=E();alias={};deleted=[]
 if flow_mode=='path':
  partition={tag:[i for i,(a,b,l)in enumerate(edges)if ('internal'if a and b else'last'if a else'first'if b else'hub')==tag]for tag in ('internal','first','last','hub')}
  states={v for a,b,l in edges for v in(a,b)if v};assert states==set(range(1,len(states)+1))
  assert all(sum(a==v for a,b,l in edges)==sum(b==v for a,b,l in edges)==1 for v in states)
  assert all(b==a+1 for a,b,l in edges if a and b)
  rawgroups={tag:em.total([hats[i]for i in ids])for tag,ids in partition.items()}
  check1=em.gate('+',rawgroups['internal'],rawgroups['first']);checksum=em.gate('+',check1,rawgroups['last']);alias['computed_J']=em.gate('-',checksum,n)
  def weighted(tag,coordinate):
   terms=sorted((edges[i][coordinate],i)for i in partition[tag])
   if len(terms)>=2 and terms[1][0]==terms[0][0]+1:
    least=terms[0][0];values=[em.gate('*',least,rawgroups[tag])]+[em.gate('*',c-least,hats[i])for c,i in terms[1:]]
   else:values=[em.gate('*',c,hats[i])for c,i in terms]
   return em.total(values)
  common=em.gate('-',weighted('internal',0),sum(states));alias['controller__flow_left']=em.gate('+',common,weighted('last',0))
  first=sorted((edges[i][1],i)for i in partition['first']);assert first[0][0]==1
  dst=em.total([common,check1]+[em.gate('*',c-1,hats[i])for c,i in first[1:]])
  alias['controller__flow_right']=em.gate('*','B',dst)
 else:
  groups={k:[i for i,e in enumerate(edges)if e[1]==k]for k in sorted({e[1]for e in edges})};rawgroups={k:em.total([hats[i]for i in ids])for k,ids in groups.items()};checksum=em.total(list(rawgroups.values()));alias['computed_J']=em.gate('-',checksum,n)
  def weighted(coordinate):
   terms=[]
   for a in sorted({e[coordinate]for e in edges}-{0}):
    raw=rawgroups[a]if coordinate==1 else em.total([hats[i]for i,e in enumerate(edges)if e[coordinate]==a]);terms.append(em.gate('*',a,raw))
   return em.gate('-',em.total(terms),sum(e[coordinate]for e in edges))
  alias['controller__flow_left']=weighted(0);alias['controller__flow_right']=em.gate('*','B',weighted(1))
 def power(k):
  if k not in POW:POW[k]=em.gate('*',power(k//2),power(k-k//2))
  return POW[k]
 def repunit(k):
  if k==0:return 0
  if k not in reps:
   a=1<<(k.bit_length()-1)
   if k==a:reps[k]=em.gate('*',repunit(k//2),em.gate('+',power(k//2),1))
   else:reps[k]=em.gate('+',repunit(a),em.gate('*',power(a),repunit(k-a)))
  return reps[k]
 def polynomial(cs):
  cs=list(cs)
  while cs and cs[-1]==0:cs.pop()
  if not cs:return 0
  if all(a==1 for a in cs):return repunit(len(cs))
  nz=[i for i,a in enumerate(cs)if a!=0];z=cs[nz[-1]];at=nz[-1]
  for i in reversed(nz[:-1]):z=em.gate('+',cs[i],em.gate('*',power(at-i),z));at=i
  return em.gate('*',power(at),z)
 counts=[sum(e[2]==label for e in edges)for label in range(1,9)]
 raw=[em.total([hats[i]for i,e in enumerate(edges)if e[2]==label])for label in range(1,9)]
 for i in range(4):alias['history__dS'+str(i)]=em.gate('-',em.gate('-',raw[2*i],raw[2*i+1]),counts[2*i]-counts[2*i+1])
 # Paid compact even/odd-pair bias for these inverse-closed tables.
 if all(counts[2*i]==counts[2*i+1]for i in range(4))and counts[2]==counts[6]==1:
  inner=em.gate('*','controller__lane_factor2',em.gate('+',power(2),counts[4]))
  inner=em.gate('+',inner,counts[0]-counts[4]);bias=em.gate('*','controller__lane_factor0',inner)
 else:bias=polynomial(counts)
 S=em.gate('-',polynomial(raw),bias);alias['physical_Sbatch']=S
 if positions is None:positions=list(range(n))
 lanes=[0]*m;occupied=[0]*m
 for i,p in enumerate(positions):lanes[p]=hats[i];occupied[p]=1
 if pack_mode=='direct':C=em.gate('-',polynomial(lanes),polynomial(occupied))
 elif pack_mode=='grouped':
  terms=[S];bydelta={}
  for i,pos in enumerate(positions):
   ell=edges[i][2]-1
   if pos!=ell:bydelta.setdefault(pos-ell,[]).append(i)
  for delta,ids in sorted(bydelta.items()):
   coeff=[0]*m;biascoeff=[0]*m
   for i in ids:
    k=edges[i][2]-1 if delta>0 else positions[i];coeff[k]=em.gate('+',coeff[k],hats[i]);biascoeff[k]+=1
   low=next(i for i,c in enumerate(biascoeff)if c)
   inner=em.gate('-',polynomial(coeff[low:]),polynomial(biascoeff[low:]));inner=em.gate('*',power(low),inner)
   diff=em.gate('-',power(delta),1)if delta>0 else em.gate('-',1,power(-delta))
   terms.append(em.gate('*',diff,inner))
  C=em.total(terms)
 else:
  terms=[S]
  for i,p in enumerate(positions):
   ell=edges[i][2]-1
   if p!=ell:terms.append(em.gate('*',em.gate('-',hats[i],1),em.gate('-',power(p),power(ell))))
  C=em.total(terms)
 alias['controller__edge_word']=C
 Rm=repunit(m);Pm=power(m)
 retained=[]
 for name,op,a,b in T['source']:
  if name.startswith(('controller__flow','selection__Spack'))or name in alias or name=='range_total_scale':deleted.append(name);continue
  if name=='selection__Mbatch':b=S
  if name=='controller__origin_mask':b=Rm
  if name=='joint_scale':b=Pm
  if name=='range_body_scale':b=Pm
  if name=='range_Bminus_shift':b=2
  if name=='selection__q':a,b=32,'range_Bshift'
  if name=='shifted_native_quotient':b='packed_z_product'
  retained.append([name,op,a,b])
 rows=retained+em.rows+copy.deepcopy(T['polynomial_finalizer']);free=['x']+[a for a in T['auxiliaries']if not a.startswith('controller__edge_hat')]+hats
 def sub(v):
  seen=set()
  while v in alias:
   assert v not in seen;seen.add(v);v=alias[v]
  return v
 rows=[[q,o,sub(a),sub(b)]for q,o,a,b in rows]
 # Resolve literal zero/one propagation only; do not uncharge other gates.
 available=set(free);pending=rows;sortedrows=[]
 while pending:
  rest=[];progress=False
  for name,op,a,b in pending:
   a,b=sub(a),sub(b)
   if any(type(v)is str and v not in available for v in(a,b)):rest.append([name,op,a,b]);continue
   if op=='*'and(a==0 or b==0):alias[name]=0
   elif op=='*'and a==1:alias[name]=b
   elif op=='*'and b==1:alias[name]=a
   elif op in('+','-')and b==0:alias[name]=a
   elif op=='+'and a==0:alias[name]=b
   elif op=='-'and a==b:alias[name]=0
   else:sortedrows.append([name,op,a,b]);available.add(name)
   progress=True
  assert progress,rest;pending=rest
 # Strictly private dead cone deletion; keep every supplied variable live.
 defs={r[0]:r for r in sortedrows};live=set();todo=['joint_outer_output'];used=set()
 while todo:
  v=todo.pop()
  if type(v)is int:continue
  if v not in defs:used.add(v)
  elif v not in live:live.add(v);todo+=defs[v][2:]
 assert used==set(free),(set(free)-used,used-set(free))
 sortedrows=[r for r in sortedrows if r[0]in live]
 return dict(edges=[list(e)for e in edges],source=sortedrows,free=free,comparisons=[[sub(a),sub(b)]for a,b in T['comparisons']],cuts={**{k:sub(v)for k,v in alias.items()if k in ['computed_J','controller__edge_word','physical_Sbatch','controller__flow_left','controller__flow_right']or k.startswith('history__dS')},**{k:k for k in ('controller__origin_mask','joint_scale','range_body_scale')}},m=m,positions=positions,graph_instruction_names=[r[0]for r in em.rows],ledger=ledger(sortedrows,free,['joint_outer_output']))

def lane_maps(edges,m):
 n=len(edges);maps=[list(range(n))]
 for reverse in(False,True):
  order=sorted(range(n),key=lambda i:(edges[i][2],-i if reverse else i));p=[None]*n
  for j,i in enumerate(order):p[i]=j
  maps.append(p)
  count=Counter();p=[None]*n;taken=set()
  for i in (range(n-1,-1,-1)if reverse else range(n)):
   label=edges[i][2];pos=label-1+8*count[label];count[label]+=1
   if pos<m:p[i]=pos;taken.add(pos)
  unused=iter(sorted(set(range(m))-taken))
  for i in range(n):
   if p[i]is None:p[i]=next(unused)
  maps.append(p)
 return [list(p)for p in dict.fromkeys(tuple(p)for p in maps)]


def poly_atom(v):return {(v,):1}if type(v)is str else({():v}if v else{})

def poly_op(op,a,b):
 out=Counter()
 if op=='*':
  for u,c in a.items():
   for v,d in b.items():out[tuple(sorted(u+v))]+=c*d
 else:
  out.update(a)
  for v,d in b.items():out[v]+=d if op=='+'else-d
 return {m:c for m,c in out.items()if c}

def formal_graph_cuts(p):
 defs={n:(o,a,b)for n,o,a,b in p['source']};env={};cutbase={P,'B'}
 def value(v):
  if type(v)is int or v in cutbase or v not in defs:return poly_atom(v)
  if v not in env:
   o,a,b=defs[v];env[v]=poly_op(o,value(a),value(b))
  return env[v]
 def total(xs):
  z={}
  for x in xs:z=poly_op('+',z,x)
  return z
 def power(k):
  z=poly_atom(1)
  for _ in range(k):z=poly_op('*',z,poly_atom(P))
  return z
 E=[poly_op('-',poly_atom('controller__edge_hat'+str(i+1)),poly_atom(1))for i in range(len(p['edges']))]
 wanted={'computed_J':total(E),'physical_Sbatch':total([poly_op('*',e,power(edge[2]-1))for e,edge in zip(E,p['edges'])]),'controller__edge_word':total([poly_op('*',e,power(pos))for e,pos in zip(E,p['positions'])]),'controller__flow_left':total([poly_op('*',poly_atom(edge[0]),e)for edge,e in zip(p['edges'],E)]),'controller__flow_right':poly_op('*',poly_atom('B'),total([poly_op('*',poly_atom(edge[1]),e)for edge,e in zip(p['edges'],E)]))}
 wanted['controller__origin_mask']=poly_op('*',wanted['computed_J'],total([power(i)for i in range(p['m'])]))
 wanted['joint_scale']=power(p['m']+8);wanted['range_body_scale']=power(2*p['m']+8)
 for k in range(4):wanted['history__dS'+str(k)]=total([poly_op('*',poly_atom(int(edge[2]==2*k+1)-int(edge[2]==2*k+2)),e)for edge,e in zip(p['edges'],E)])
 need(set(wanted)==set(p['cuts']),'complete graph interface cut list')
 for k,q in wanted.items():need(value(p['cuts'][k])==q,'entire graph coefficient identity '+k)
 return dict(exact_coefficient_identities=len(wanted),coefficient_terms=sum(map(len,wanted.values())),formal_ports=sorted(wanted))

def full_interface_identity(T,p):
 # A literal saved static program with nine formal graph ports is the
 # specification. All graph polynomials above are proved independently.
 reference=[]
 for n,o,a,b in T['source']+T['polynomial_finalizer']:
  if n.startswith(('controller__flow','selection__Spack'))or n in p['cuts']or n=='range_total_scale':continue
  if n=='selection__Mbatch':b='physical_Sbatch'
  if n=='range_Bminus_shift':b=2
  if n=='selection__q':a,b=32,'range_Bshift'
  if n=='shifted_native_quotient':b='packed_z_product'
  reference.append([n,o,a,b])
 interned={};nodes={}
 def intern(t):
  if t not in interned:interned[t]=len(interned);nodes[interned[t]]=t
  return interned[t]
 zero=intern(('int',0));one=intern(('int',1))
 def op(o,a,b):
  if o=='*'and(a==zero or b==zero):return zero
  if o=='*'and a==one:return b
  if o=='*'and b==one:return a
  if o in('+','-')and b==zero:return a
  if o=='+'and a==zero:return b
  if o=='-'and a==b:return zero
  if nodes[a][0]==nodes[b][0]=='int':
   av,bv=nodes[a][1],nodes[b][1];return intern(('int',av*bv if o=='*'else av+bv if o=='+'else av-bv))
  return intern((o,*sorted((a,b))))if o in('+','*')else intern((o,a,b))
 def run(rows,actual):
  e={n:intern(('input',n))for n in p['free']};overrides={}
  for k,v in p['cuts'].items():
   token=intern(('int',v))if type(v)is int else intern(('proved_cut',k))
   if actual and type(v)is str:overrides[v]=token
   elif not actual:e[k]=token
  pending=list(rows)
  while pending:
   rest=[]
   for n,o,a,b in pending:
    if any(type(v)is str and v not in e for v in(a,b)):rest.append([n,o,a,b]);continue
    av=e[a]if type(a)is str else intern(('int',a));bv=e[b]if type(b)is str else intern(('int',b));e[n]=overrides.get(n,op(o,av,bv))
   need(len(rest)<len(pending),'formal full-DAG closure');pending=rest
  return e
 a=run(reference,False);b=run(p['source'],True)
 # Compiler zero/one aliases can remove static rows. Every surviving static
 # row, each complete comparison and the final output must still agree.
 checked=0
 for n,o,x,y in p['source']:
  if n in a:need(a[n]==b[n],'complete retained static expression '+n);checked+=1
 for (x,y),(u,v)in zip(T['comparisons'],p['comparisons']):
  av=lambda e,w:e[w]if type(w)is str else intern(('int',w))
  need(op('-',av(a,x),av(a,y))==op('-',av(b,u),av(b,v)),'whole comparison expression')
 need(a['joint_outer_output']==b['joint_outer_output'],'whole output interface identity')
 return dict(complete_static_register_identities=checked,complete_comparison_identities=6,whole_output_identity=True)

def exact_degree(p):
 rows=p['source'];defs={n:(o,a,b)for n,o,a,b in rows};X,A,c,g,H='selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5'
 expected={'selection__R15':('-','selection__L15','selection__Ac2'),'selection__L15':('*','selection__R14','selection__R14'),'selection__R14':('+','selection__D1',g),'selection__D1':('+',X,'selection__cam2'),'selection__cam2':('*',c,A),'selection__A':('+','selection__a_square',H),'selection__a_square':('*',A,A),H:('+','selection__a4',3),'selection__a4':('*',4,A),g:('*','selection__ga',H),'selection__Ac2':('*','selection__A','selection__c2'),'selection__c2':('*',c,c)}
 need(all(defs[n]==v for n,v in expected.items()),'literal guarded main norm cone')
 prime=1000000007;rng=random.Random(714);weights={n:rng.randrange(1,100)for n in sorted(p['free'])};env={n:(1,w)for n,w in weights.items()}
 def add(a,b,sign=1):
  d=max(a[0],b[0]);return d,((a[1]if a[0]==d else 0)+sign*(b[1]if b[0]==d else 0))%prime
 def mul(a,b):return a[0]+b[0],a[1]*b[1]%prime
 for n,o,a,b in rows:
  av=env[a]if type(a)is str else(0,a%prime);bv=env[b]if type(b)is str else(0,b%prime)
  if n=='selection__R15':
   xx,aa,cc,gg,hh=[env[v]for v in(X,A,c,g,H)]
   terms=[mul(xx,xx),mul((0,2),mul(mul(xx,aa),cc)),mul((0,2),mul(xx,gg)),mul((0,2),mul(mul(aa,cc),gg)),mul(gg,gg),mul((0,-1),mul(hh,mul(cc,cc)))]
   z=terms[0]
   for term in terms[1:]:z=add(z,term)
  else:z=mul(av,bv)if o=='*'else add(av,bv,1 if o=='+'else-1)
  env[n]=z
 target=73+2*(29*(2*p['m']+8)+7*p['m']+106)
 need(env['joint_outer_output'][0]==target and env['joint_outer_output'][1]!=0,'attained complete fixed-numeral exact degree1789')
 need(sum(env[n][0]for n in FACTORS)+6==target,'actual seven factors and outer degree')
 return dict(exact_degree=target,guarded_upper=target,naive_upper=p['ledger']['degree_upper'],factor_degrees={n:env[n][0]for n in FACTORS},prime=prime,weights=weights,nonzero_full_leader=env['joint_outer_output'][1],scope='All supplied coordinates including x have degree1; fixed24,13 and all compiler numerals degree0.')

def path_for_word(edges,word):
 states={0:[]}
 for label in word:
  nxt={}
  for st,path in sorted(states.items()):
   for i,(a,b,l)in enumerate(edges):
    if a==st and l==label and b not in nxt:nxt[b]=path+[i]
  states=nxt
 need(0 in states,'actual accepting control path');return states[0]


def check_numeric(p,case):
 rng=random.Random(234+case);v={n:rng.randrange(-1,3)for n in p['free']}
 if case>=4:v={n:Fraction(k,3)for n,k in v.items()}
 e=execute(p['source'],v);b=e['B'];pv=e[P];EE=[v['controller__edge_hat'+str(i+1)]-1 for i in range(len(p['edges']))]
 expected={'computed_J':sum(EE),'physical_Sbatch':sum(z*pv**(edge[2]-1)for z,edge in zip(EE,p['edges'])),'controller__edge_word':sum(z*pv**pos for z,pos in zip(EE,p['positions'])),'controller__flow_left':sum(edge[0]*z for z,edge in zip(EE,p['edges'])),'controller__flow_right':b*sum(edge[1]*z for z,edge in zip(EE,p['edges'])),'controller__origin_mask':sum(EE)*sum(pv**i for i in range(p['m'])),'joint_scale':pv**(p['m']+8),'range_body_scale':pv**(2*p['m']+8)}
 for k in range(4):expected['history__dS'+str(k)]=sum((int(edge[2]==2*k+1)-int(edge[2]==2*k+2))*z for z,edge in zip(EE,p['edges']))
 for k,value in expected.items():
  port=p['cuts'][k];need((e[port]if type(port)is str else port)==value,'numeric cut '+k)
 res=[(e[a]if type(a)is str else a)-(e[b]if type(b)is str else b)for a,b in p['comparisons']]
 need(e['joint_outer_output']==e['eight_units']*(1+sum(z*z for i,z in enumerate(res)if i!=4))-1,'all six comparisons/full paid finalizer')
 return dict(rational=case>=4)

def matrix(word):
 a=[[int(i==j)for j in range(4)]for i in range(4)]
 for label in word:
  k=(label-1)//2;a[k]=[x+(1 if label%2 else-1)*y for x,y in zip(a[k],a[k^1])]
 return a

def matmul(a,b):return [[sum(a[i][k]*b[k][j]for k in range(4))for j in range(4)]for i in range(4)]

def language_facts():
 identity=matrix(());r=matrix(RT);u=matrix(U);bm=matrix(BMAC);am=matrix(AMAC)
 need(r==[[1,-1,0,0],[1,0,0,0],[0,0,1,-1],[0,0,1,0]],'literal Rtilde action')
 need(bm==[[1,5,0,0],[0,1,0,0],[0,0,1,5],[0,0,0,1]],'literal U^5 action')
 need(am==matmul(bm,r),'chronological A=Rtilde B')
 for word in CODES+NIELSEN:need(matmul(matrix(inv(word)),matrix(word))==identity,'literal physical inverses')
 # Nielsen equalities use physical order: Rtilde = A B^-1 and Rtilde^-1 = B A^-1.
 need(matrix(AMAC+inv(BMAC))==r and matrix(BMAC+inv(AMAC))==matrix(inv(RT)),'Nielsen subgroup identities')
 orbit=[];v=[0,1]
 for k in range(6):orbit.append(v);v=[(v[0]-v[1])%5,v[0]]
 need(v==[0,1]and len(set(map(tuple,orbit)))==6,'exact six element mod5 endpoint orbit')
 residues=sorted({y for x,y in orbit if x==1});need(residues==[0,1],'necessary ordinary input residues')
 need((24*1+13)%5 not in residues,'x1 is excluded')
 return dict(Rtilde=list(RT),U=list(U),codes=[list(w)for w in CODES],nielsen_codes=[list(w)for w in NIELSEN],matrix_Rtilde=r,matrix_B=bm,matrix_A=am,mod5_endpoint_orbit=orbit,sufficient_input_residue_mod5=2,necessary_input_residues_mod5=[2,3],rejected_positive_input=1,exact_input_language_claimed=False)

def outer_history(p,x):
 need(x>0 and x%5==2,'sufficient accepted residue class')
 u=24*x+13;exponent=(u-1)//5;word=RT+BMAC*exponent
 # Same physical word is A B^(exponent-1) and the Nielsen word Rtilde B^exponent.
 need(exponent>=1 and word==AMAC+BMAC*(exponent-1),'explicit accepted macro decomposition')
 path=path_for_word(p['edges'],word);state=[1,u,1,u];states=[list(state)]
 for label in word:
  k=(label-1)//2;state=list(state);state[k]+=(1 if label%2 else-1)*state[k^1];states.append(state)
 need(state==[0,1,0,1],'actual ordinary-input accepting endpoint')
 D=128
 while D<=max(u,1+max(abs(v)for st in states for v in st)):D*=2
 B=16*D;t=len(word);pv=B**t;J=sum(B**i for i in range(t));v={'x':x,'height_slack':D-u}
 for k in range(4):v['H'+str(k)]=sum((st[k]+D-1)*B**i for i,st in enumerate(states[:-1]))
 for label in range(1,9):v['Zhat'+str(label-1)]=1+sum((states[i][((label-1)//2)^1]+D-1)*B**i for i,l in enumerate(word)if l==label)
 for edge in range(len(p['edges'])):v['controller__edge_hat'+str(edge+1)]=1+sum(B**i for i,j in enumerate(path)if j==edge)
 v['selection__bound_global']=pv+1-sum(v['H'+str(i)]for i in range(4))-sum(v['Zhat'+str(i)]for i in range(8));need(min(v.values())>0 and B>p['m'],'genuine positive outer values and actual radix margin')
 defs={n:(o,a,b)for n,o,a,b in p['source']};env=dict(v)
 def value(a):
  if type(a)is int:return a
  if a not in env:
   o,b,c=defs[a];bv,cv=value(b),value(c);env[a]=bv*cv if o=='*'else bv+cv if o=='+'else bv-cv
  return env[a]
 need(value(P)==pv and value(p['cuts']['computed_J'])==J,'genuine duration and repunit')
 need(value(p['cuts']['controller__flow_left'])==value(p['cuts']['controller__flow_right']),'genuine chronological controller')
 H,M,Z=[value(n)for n in ('range_H','range_M','range_Z')];q=value('selection__q');Q=q//16
 need(H&M==Z and max(H,M,Z)<Q and q==32*B*pv**(2*p['m']+8),'full joined AND/product scale')
 fields=[16*(Q-H-M+Z)-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
 need(min(fields)>0 and sum(fields)==q-1,'all four positive native fields')
 for k in range(4):need(value('history__left'+str(k))==value('history__right'+str(k)),'complete genuine endpoint equation')
 need(value('joint_bound_unit')==1,'actual positive global bound slack')
 return dict(x=x,u=u,word=[int(l)for l in word],edge_path=path,duration=t,D=D,B=B,P_bit_length=pv.bit_length(),q_bit_length=q.bit_length(),native_truth_fields_positive=True,all_five_outer_residuals_zero=True,joint_bound_unit=1,native_positive_extension='inherited theorem, not materialized',full_native_pell_zero_materialized=False)

def authenticate(root):
 blobs={}
 for name,h in PINS.items():
  path=Path(root)/name
  if not path.exists():path=Path(__file__).resolve().parent/name
  data=path.read_bytes();need(sha(data)==h,'pin '+name);blobs[name]=data
 return blobs

def bouquet_certificate(edges):
 edges=[tuple(e)for e in edges];need(len(edges)==28 and len(set(edges))==28,'literal inverse bouquet edge count')
 need({v for a,b,l in edges for v in(a,b)}==set(range(13)),'actual thirteen states')
 need(all((b,a,l+1 if l%2 else l-1)in edges for a,b,l in edges),'inverse closure')
 need(len({(a,l)for a,b,l in edges})==28,'deterministic inverse graph')
 cycles=[]
 for word in(RT,BMAC):
  path=path_for_word(edges,word);states=[0]+[edges[i][1]for i in path]
  need(states[-1]==0 and len(set(states[:-1]))==len(word),'literal simple generator cycle')
  cycles.append((path,states))
 need(set(cycles[0][1][1:-1]).isdisjoint(cycles[1][1][1:-1]),'cycles meet only at distinguished hub')
 used={edges[i]for path,states in cycles for i in path};used|={(b,a,l+1 if l%2 else l-1)for a,b,l in list(used)}
 need(used==set(edges),'all edges are the two cycles and their inverses')
 return dict(states=13,directed_edges=28,cycle_lengths=[4,10],generator_paths=[p for p,s in cycles],nonhub_degree=2,subgroup_basis=['Rtilde','B'])

def verify(root):
 blobs=authenticate(root);T=json.loads(blobs['group_projective_label_aligned_lanes.json'])['source']['source_example']
 need(T['m']==8 and T['compute_length']is True and T['codes']==[[8,6,4,2,7,5,3,1]],'actual saved complete eight-lane source')
 prefix=[['history__input_product','*',24,'x'],['history__u','+','history__input_product',13],['D','+','history__u','height_slack'],['history__c0','-','D',1],['B','*',16,'D']]
 need(T['source'][:5]==prefix,'actual ordinary input and positive height interface')
 core=json.loads(blobs['group_inverse_stallings_controller.json'])['core']['edges']
 graphs={'private':separate(CODES)[1:],'shared':share(CODES)[0][1:],'nielsen':separate(NIELSEN)[1:],'folded':core}
 graphproof=bouquet_certificate(core);facts=language_facts();eq=language_equivalence(graphs['private'],graphs['shared'])
 counts=Counter();records=[];best={}
 for tag,edges in graphs.items():
  n=len(edges);m=8
  while m<n:m*=2
  need(n=={'private':48,'shared':30,'nielsen':28,'folded':28}[tag],'actual four edge counts')
  need(all(0<=a<m and 0<=b<m and 1<=l<=8 for a,b,l in edges),'fixed state/physical alphabet bounds')
  need({l for a,b,l in edges}==set(range(1,9)),'all eight physical generators occur')
  maps=lane_maps(edges,m);need(len(maps)==5,'five explicitly declared lane schedules')
  for positions in maps:
   need(len(set(positions))==n and min(positions)>=0 and max(positions)<m,'injective padded lane interface')
   for packing in('direct','shared','grouped'):
    p=transform(T,edges,'path'if tag in('private','nielsen')else'generic',positions,packing);p.update(graph=tag,packing=packing,flow='private-path shared checksum'if tag in('private','nielsen')else'general weighted flow')
    p['formal_cuts']=formal_graph_cuts(p);p['whole_interface_identity']=full_interface_identity(T,p);p['degree_certificate']=exact_degree(p)
    p['parameters']=['x'];p['auxiliaries']=[v for v in p['free']if v!='x'];p['domains']={'parameters':'positive integers','auxiliaries':'positive integers'}
    p['ledger'].update(naive_degree_upper=p['ledger']['degree_upper'],degree_upper=p['degree_certificate']['exact_degree'],exact_degree=p['degree_certificate']['exact_degree'],certificate_operations=len(p['source'])-17,certificate_M=p['ledger']['M']-6,certificate_A=p['ledger']['A']-11,finalizer_operations=17,comparisons=6,positive_witnesses=len(p['auxiliaries']),controller_states=len({a for e in edges for a in e[:2]}))
    need(len(p['free'])==n+27 and len(p['comparisons'])==6,'all supplied parameters/witnesses/comparisons paid')
    rows={r[0]:r for r in p['source']};need(all(rows[name]==[name,o,p['cuts'].get(a,a),p['cuts'].get(b,b)]for name,o,a,b in T['polynomial_finalizer']),'all seventeen finalizer rows retained')
    need(all(row in p['source']for row in prefix),'same literal height/ordinary input')
    counts['complete_sources']+=1;counts['paid_live_gates']+=len(p['source']);counts['exact_graph_and_scale_polynomials']+=12;counts['whole_comparisons']+=6;counts['whole_static_register_identities']+=p['whole_interface_identity']['complete_static_register_identities'];counts['exact_degree_certificates']+=1
    key=(p['ledger']['operations'],p['ledger']['M'],packing,positions)
    if tag not in best or key<best[tag][0]:best[tag]=key,p
    records.append(dict(graph=tag,positions=positions,packing=packing,m=m,source_sha256=sha(json.dumps(p['source'],separators=(',',':')).encode()),ledger=p['ledger']))
 packets={tag:p for tag,(key,p)in best.items()};outer=[]
 for tag,p in packets.items():
  for case in range(6):r=check_numeric(p,case);counts['complete_numeric_outputs']+=1;counts['rational_outputs']+=r['rational']
  for x in(2,7):r=outer_history(p,x);r['graph']=tag;outer.append(r);counts['genuine_accepting_outer_histories']+=1
 need([(packets[t]['ledger']['operations'],packets[t]['ledger']['M'],packets[t]['ledger']['A'])for t in graphs]==[(492,191,301),(432,178,254),(371,150,221),(376,147,229)],'four complete literal winner ledgers')
 need(len(records)==60 and len(packets)==4,'finite sixty-schedule scope/four whole saved arrays')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),counts=dict(counts),matrix_language=facts,exact_private_shared_language_subset_pairs=eq,inverse_bouquet=graphproof,ordinary_prefix=prefix,records=records,packets=packets,accepting_outer_histories=outer,scope='Four complete fixed-table positive-integer projective sources. Private492/shared432 preserve exact macro words; Nielsen371/folded376 preserve matrix subgroup and the existential ordinary-input predicate. Proper nonempty language with x2 accepted and x1 excluded. Sixty declared schedules only; no global optimality, numerical universality, cross-graph polynomial identity, cross-graph zero-fiber bijection, or materialized native Pell zero.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],ledgers={k:p['ledger']for k,p in r['packets'].items()})))
if __name__=='__main__':main()
