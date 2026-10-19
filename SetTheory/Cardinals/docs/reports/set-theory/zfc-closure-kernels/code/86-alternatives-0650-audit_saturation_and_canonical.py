#!/usr/bin/env python3
"""Independent structural matcher and finite reference checks, no producer writes."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import sys,json,random,itertools,hashlib,copy
V=Path(__file__).resolve().parent;R=V.parent
sys.path.insert(0,str(R/'logical_routes'))
import forward_saturation as S
import canonical_arena as A
import square_pair_conjugacy as B

def direct(nodes,root,rule):
    # Full-tag simultaneous unification, no leaf-path oracle or representative paths.
    env={};todo=[(S.ORACLE['syntax'][rule],root)]
    while todo:
        pat,i=todo.pop();tag=pat[0]
        if tag=='z':
            if i!=0:return None
        elif tag=='p':
            j=pat[1]
            if j in env and env[j]!=i:return None
            env[j]=i
        else:
            t,l,r=(0,0,0)if i==0 else nodes[i][1:]
            if t!=tag:return None
            todo.append((pat[1],l));todo.append((pat[2],r))
    args=[env[j]for j in range(S.T[rule].arity)]
    if rule==11 and(args[2]==args[0]or args[2]==args[1]):return None
    return args

def compare(nodes,root,rule):
    expect=direct(nodes,root,rule)
    assert S.recognize(nodes,root,rule)==expect
    assert S.recognize_by_markers(nodes,root,rule)==(expect is not None)
    return expect is not None

counts={'prefix_root_checks':0,'sparse_root_checks':0,'generated_nodes':0,'distinguishing_witnesses':0,'independent_sweeps':0}
positive=0
for pairing in('cantor','square'):
 nodes=A.generated_prefix(767,pairing=pairing)
 vals=A.native_values(nodes);assert len(set(vals))==len(nodes)
 assert vals==([B.f(i)for i in range(len(nodes))]if pairing=='square'else list(range(len(nodes))))
 counts['generated_nodes']+=len(nodes)
 for i in range(len(nodes)):
  for rule in S.T:positive+=compare(nodes,i,rule);counts['prefix_root_checks']+=1
rng=random.Random(654321)
for _ in range(60):
 nodes=[['z']];intern={}
 for i in range(1,15):
  while True:
   x=(rng.randrange(4),rng.randrange(len(nodes)),rng.randrange(len(nodes)))
   if x!=(0,0,0)and x not in intern:break
  intern[x]=len(nodes);nodes.append(['b',*x])
 rule=rng.choice(list(S.T));args=[rng.randrange(15)for _ in range(S.T[rule].arity)]
 root=S.O.make_instance(S.ORACLE['syntax'][rule],args,nodes,intern)
 for candidate in {0,root,*[rng.randrange(len(nodes))for _ in range(20)]}:
  for rule2 in S.T:positive+=compare(nodes,candidate,rule2);counts['sparse_root_checks']+=1
 # Canonical injectivity licenses exact old-format distinguishing paths.
 for _ in range(12):
  a,b=rng.sample(range(len(nodes)),2);path=A.O.witness(nodes,a,b)
  assert path is not None and A.C.distinguish(nodes,a,b,path,{'path_edges':0})
  counts['distinguishing_witnesses']+=1

def independent_sweep(nodes,flags):
 flags=list(flags);halt=False
 for i,node in enumerate(nodes):
  tag,l,r=(0,0,0)if i==0 else node[1:]
  if tag==0:
   if not flags[i] and any(direct(nodes,i,rule)is not None for rule in S.T):flags[i]=True
   if flags[i]and flags[l]:
    flags[r]=True
    if r==1:halt=True
  elif tag==2 and flags[r]:flags[i]=True
  if halt:break
 return flags,halt
search=S.Search(audit=True)
for _ in range(180):
 expected,h=independent_sweep(search.nodes,search.proved)
 search.advance();assert search.proved[:len(expected)]==expected and search.halted==h
 assert A.native_values(search.nodes)==list(range(len(search.nodes)))
 # Independently verify each diagnostic axiom by full-tag unification.
 for row in search.rows:
  if row['tag']>=3:assert direct(search.nodes,row['formula'],row['tag'])==row['args']
 counts['independent_sweeps']+=1
for _ in range(100):
 nodes=A.generated_prefix(rng.randrange(2,160),pairing='cantor');flags=[bool(rng.randrange(2))for _ in nodes];flags[0]=True;flags[1]=False
 p=S.Search();p.nodes=nodes;p.proved=flags.copy()
 expected,h=independent_sweep(nodes,flags);p.sweep();assert p.proved==expected and p.halted==h
 counts['independent_sweeps']+=1
# Fresh original finite tests are supplementary; avoid their __main__ writers.
fresh={'saturation':S.tests(),'canonical':A.tests(),'square':B.tests()}
paths=[R/'logical_routes'/f for f in('forward_saturation.md','forward_saturation.py','canonical_arena.md','canonical_arena.py','square_pair_conjugacy.md','square_pair_conjugacy.py')]
report={'status':'PASS','independent':counts,'positive_recognitions':positive,'fresh_producer_tests':fresh,'hashes':{str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},'scope':'Finite diagnostics plus separate ordinary universal proof review; no literal machine claim.'}
(V/'saturation_and_canonical_independent_audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
