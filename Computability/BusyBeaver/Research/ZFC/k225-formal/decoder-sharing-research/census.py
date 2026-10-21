#!/usr/bin/env python3
"""Own bounded finite decoder-prefix census; no imported project executable code.
This does not prove Lean lemmas or certify a changed checker.
"""
from pathlib import Path
from collections import Counter, defaultdict
import hashlib, json, time
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
P=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k215'
S=P/'sites215.json'; M=P/'k215.native.tm'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads(S.read_text()); leaves={r[0]:tuple(r[1:]) for r in rows}
assert len(leaves)==len(rows)==4751
inner={p[:i] for p in leaves for i in range(len(p))}
assert len(inner)==4750 and not(inner & set(leaves))
T={}
for l in M.read_text().splitlines():
 if not l or l.startswith('#'):continue
 q,b,w,d,t=l.split(); T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(t))
assert len(T)==430
nodes={}; ids={}; nodeid={}
def intern(p):
 n=leaves[p] if p in leaves else (intern(p+'0'),intern(p+'1'))
 if n not in ids:ids[n]=len(ids)
 nodeid[p]=ids[n]; nodes[p]=n
 return ids[n]
intern('')
# Independently replay only a decoder internal-to-internal edge. The known tape
# is exactly the read pointer prefix and the start marker; all external cells
# are absent, so every outside read fails. Record initial bits for every cell
# actually read, including cells written before their first read, for a simple
# sufficient whole-tape local-pattern precondition.
physical={'':84}; local=defaultdict(list); traces={}; contexts=defaultdict(list)
start=time.monotonic()
for p in sorted(inner,key=lambda x:(len(x),x)):
 assert p in physical
 q0=physical[p]
 for b in '01':
  c=p+b
  if c not in inner:continue
  initial={-1:1,**{i:int(v) for i,v in enumerate(c)}}
  tape=dict(initial); h=len(p); q=q0; read=set(); trace=[]
  for steps in range(100):
   if h==len(c):break
   assert h in tape,(p,b,q,h,'outside')
   read.add(h); w,d,t=T[q,tape[h]]
   trace.append((q,h-len(p),tape[h],w,d,t));tape[h]=w;h+=d;q=t
  else:raise AssertionError(('fuel',p,b))
  assert tape==initial and h==len(c) and steps>0
  req=tuple(sorted((i-len(p),initial[i]) for i in read))
  key=(q0,req,q,tuple(trace))
  local[key].append(c);traces[c]=trace;physical[c]=q
  contexts[q0,int(b)].append((c,req,q))
assert len(traces)==4749 and len(physical)==4750
# Edge ports follow literal RegisterPath, including empty-prefix behavior.
def inc(p):
 r=list(p)
 for i in range(len(r)-1,-1,-1):
  if r[i]=='0':r[i]='1';return ''.join(r)
  r[i]='0'
 return ''.join(r)
def strip(p,b,k):
 while k and p:
  k-=p[-1]==b;p=p[:-1]
 return p
ports={}
for p,e in leaves.items():
 op=e[0];a=e[1]if len(e)>1 else None
 if op=='CI':ps=[('inc',inc(p),all(x=='1'for x in p))]
 elif op=='CD':
  t=strip(p,'0',1);ps=[('zero',inc(t),all(x=='1'for x in t)),('positive',inc(p),all(x=='1'for x in p))]
 elif op=='CB':
  t=strip(p,'0',a);ps=[('break',inc(t),all(x=='1'for x in t))]
 elif op=='CC':ps=[('continue',strip(p,'1',a),False)]
 elif op=='CH':ps=[('halt',None,None)]
 else:raise AssertionError(e)
 ports[p]=ps
# Retain a concrete counterexample to state+read-bit being enough for a local
# dispatcher-edge proof, and a repeated subtree with escaping CC endpoints.
collisions=[]
for (q,b),v in contexts.items():
 if len({(req,target)for _,req,target in v})>1:
  samples=[];seen=set()
  for path,req,target in v:
   if (req,target)not in seen:samples.append({'path':path,'required_relative_bits':req,'target':target});seen.add((req,target))
  collisions.append({'state':q,'bit':b,'classes':len(seen),'samples':samples[:4]})
subgroups=defaultdict(list)
for p in inner:subgroups[nodeid[p]].append(p)
escape=[]
for nid,ps in subgroups.items():
 if len(ps)<2:continue
 # Shortest internal subtree that contains a continue leaving its occurrence.
 for p in sorted(ps):
  for q in sorted(leaves):
   if q.startswith(p)and leaves[q][0]=='CC'and not ports[q][0][1].startswith(p):
    escape.append((len(q)-len(p),nid,p,q,ports[q][0][1],leaves[q]))
    break
  if escape and escape[-1][1]==nid:break
examples=[]
for _,nid,p,q,target,e in sorted(escape)[:1]:
 suffix=q[len(p):]
 for p2 in sorted(subgroups[nid])[:3]:
  q2=p2+suffix;examples.append({'subtree_id':nid,'subtree_prefix':p2,'leaf_path':q2,'leaf':leaves[q2],'target':ports[q2][0][1]})
# All CD branches share exact pre-oracle configuration and decoder trace. A
# branch-independent dispatcher theorem can therefore be instantiated twice.
r={'status':'FINITE_CENSUS_ONLY','scope':'Exact literal internal-prefix traces and RegisterPath ports; no primitive runtime, proof-kernel or speedup claim.',
 'inputs':{str(p.relative_to(ROOT)):sha(p)for p in[S,M]},'script_sha256':sha(Path(__file__)),
 'leaf_occurrences':len(leaves),'internal_occurrences':len(inner),'shared_tree_nodes_including_leaves':len(ids),'shared_internal_nodes':len({nodeid[p]for p in inner}),'primitive_leaf_kinds':len(set(leaves.values())),
 'symbolic_cases':sum(len(x)for x in ports.values()),'decrement_occurrences':sum(e[0]=='CD'for e in leaves.values()),
 'internal_edge_occurrences':len(traces),'physical_internal_states':len(set(physical.values())),
 'literal_local_frame_trace_classes':len(local),'sum_local_steps_all_edges':sum(len(x)for x in traces.values()),'sum_steps_one_per_frame_class':sum(len(k[3])for k in local),
 'local_trace_length_counts':dict(sorted(Counter(len(x)for x in traces.values()).items())),
 'required_left_context_depth_counts':dict(sorted(Counter(max(0,-min(i for i,_ in k[1]))for k in local).items())),
 'state_bit_context_collisions':collisions,'same_subtree_external_continue_examples':examples,
 'seconds':time.monotonic()-start}
Path(__file__).with_name('result.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
