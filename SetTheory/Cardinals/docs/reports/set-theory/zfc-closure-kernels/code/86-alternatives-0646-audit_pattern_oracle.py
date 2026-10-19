#!/usr/bin/env python3
"""Independent finite artifact/interface checks and adversarial matcher controls.
The universal component proof is in pattern_oracle_review.md.
"""
from pathlib import Path
import importlib.util, hashlib, itertools, json, sys
if not __debug__:raise SystemExit('Assertions must be enabled')
ROOT=Path(__file__).resolve().parents[1];A=ROOT/'architectures';OUT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('review_pattern_oracle',A/'pattern_oracle.py')
O=importlib.util.module_from_spec(spec);spec.loader.exec_module(O)
C,P,T=O.load_source();oracle=O.compile_oracle(T)
hash0=hashlib.sha256((A/'pattern_oracle.py').read_bytes()).hexdigest()

def parse(p):
 table={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert (q,b) not in table
  assert b in (0,1) and w in (0,1) and d in ('L','R');table[q,b]=(w,d,t)
 return table
assert parse(A/'template_oracle_102.tm')==oracle['table']
assert oracle['constructors']==91 and oracle['emitters']==11 and oracle['halt']==102
assert set(oracle['table'])==set(itertools.product(range(102),range(2)))
assert all(0<=v[2]<=102 for v in oracle['table'].values())

# Independent direct recursion over template occurrences and node identities.
# All actual-zero observations are the virtual tag0 constructor (0,0).
def reference(tree,out,args,nodes):
 if tree[0]=='z':return out==0
 if tree[0]=='p':return out==args[tree[1]]
 tag,l,r=(0,0,0) if out==0 else nodes[out][1:]
 return tag==tree[0] and reference(tree[1],l,args,nodes) and reference(tree[2],r,args,nodes)
def leaves(tree,path=()):
 if tree[0] in ('z','p'):return [(path,tree)]
 return leaves(tree[1],path+(0,))+leaves(tree[2],path+(1,))
def expected_edges(tree,path):
 bits=[]
 for b in path:
  bits.append((tree[0]//(1<<b))%2);tree=tree[1+b]
 return bits,0 if tree[0]=='z' else tree[1]+1

def run_literal(table,q,halt,tape,head):
 tape=dict(tape);start=head
 while q!=halt:
  w,d,q=table[q,int(tape.get(head,0))]
  assert d=='R'
  if w:tape[head]=1
  else:tape.pop(head,None)
  head+=1;assert head-start<=26
 return tape,head

counts={'leaf_occurrences':0,'whole_tape_context_tests':0,'duplicate_id_assignments':0,
 'duplicate_parameter_id_rejections':0,'internal_duplicate_acceptances':0}
for rule,t in T.items():
 tree=O.unroll(t,t.root);ll=leaves(tree)
 actual=list(O.enumerate_leaf_paths(oracle,rule))
 assert [tuple(p) for p,e,l in actual]==[p for p,t in ll]
 for (path,terminal),(p,bits,code) in zip(ll,actual):
  eb,ec=expected_edges(tree,path);assert (bits,code)==(eb,ec)
  for origin in (-11,0,7):
   # Arbitrary nonblank left context and immediate suffix; emitter must overwrite
   # its three cells, and preserve all cells beyond them.
   tape={origin-8:1,origin-1:1,origin+len(path):1,origin+len(path)+2:1,
         origin+len(path)+3:1,origin+len(path)+9:1}
   for i,b in enumerate(path):
    if b:tape[origin+i]=1
    else:tape.pop(origin+i,None)
   expected=dict(tape)
   for i,b in enumerate(eb+[int(x) for x in format(ec,'03b')]):
    if b:expected[origin+i]=1
    else:expected.pop(origin+i,None)
   end,h=run_literal(oracle['table'],oracle['roots'][rule],102,tape,origin)
   assert end==expected and h==origin+len(path)+3
   counts['whole_tape_context_tests']+=1
  counts['leaf_occurrences']+=1
 # Deliberate duplicate IDs: equal numeric/structural nodes1,4 and2,5.
 for args in itertools.product(range(6),repeat=t.arity):
  nodes=[['z'],['b',1,0,0],['b',2,0,0],['b',3,0,0],['b',1,0,0],['b',2,0,0]]
  out=O.make_instance(tree,args,nodes,{},duplicates=True)
  st={'node_records':0};C.validate_nodes(nodes,st)
  assert reference(tree,out,args,nodes)
  assert O.match_oracle(nodes,out,args,oracle,rule)
  assert O.legacy_match(P,nodes,out,args,t)
  counts['duplicate_id_assignments']+=1
  # With no constructor interning, equal internal subtrees occur as distinct IDs.
  keys=[tuple(n[1:]) for n in nodes[6:]]
  if len(keys)!=len(set(keys)):counts['internal_duplicate_acceptances']+=1
  # Changing a requested parameter to a distinct duplicate must reject if used.
  for j,a in enumerate(args):
   if a not in (1,2,4,5):continue
   new=list(args);new[j]={1:4,4:1,2:5,5:2}[a]
   expected=reference(tree,out,new,nodes)
   assert O.match_oracle(nodes,out,new,oracle,rule)==expected
   assert O.legacy_match(P,nodes,out,new,t)==expected
   if not expected:counts['duplicate_parameter_id_rejections']+=1

# Inspect the 126-state blank demonstration by an independent sparse simulator.
table=parse(A/'blank_longest_bundle_probe_126.tm');assert set(table)==set(itertools.product(range(126),range(2)))
results=json.loads((A/'pattern_oracle_results.json').read_text());path=results['blank_longest_bundle_probe']['path']
q=102;head=0;tape={};steps=0
while q!=126:
 w,d,q=table[q,int(head in tape)]
 if w:tape[head]=1
 else:tape.pop(head,None)
 head+=1 if d=='R' else -1;steps+=1;assert steps<=50
origin=1-len(path);eb,ec=expected_edges(oracle['syntax'][11],path)
expected={origin+i:1 for i,b in enumerate(eb+[int(x) for x in format(ec,'03b')]) if b}
assert tape==expected and head==4 and steps==50
assert hash0==hashlib.sha256((A/'pattern_oracle.py').read_bytes()).hexdigest()
result={'status':'PASS','counts':counts,'working_states':102,'constructors':91,'leaf_emitters':11,
 'blank_demonstration':{'working_states':126,'start':102,'halt':126,'steps':50,'head':4,'whole_tape':sorted(tape)},
 'scope':'Finite checks support the separately stated universal tree-induction proof. No full binary matcher, validator, enumerator, or consistency-search machine exists here.',
 'input_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [A/'pattern_oracle.py',A/'template_oracle_102.tm',A/'blank_longest_bundle_probe_126.tm']}}
(OUT/'pattern_oracle_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
