#!/usr/bin/env python3
"""Build and verify a finite decoder certificate with two preceding bits.

This certifies traversal of internal source nodes and binding of primitive
entries. It does not certify primitive runtime, proof enumeration, or ZFC.
All local internal blocks read/write only the explicit suffix and the
current bit, restore that window, and stop at the next cell. Thus their
finite checks quantify every exterior tape by the elementary frame argument.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, hashlib, json
if not __debug__:
 raise RuntimeError('This certificate checker requires assertions; do not run Python with -O.')
ROOT=Path(__file__).resolve().parents[1]
INPUTS=ROOT/'inputs'
SOURCE_SHA='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
TABLE_SHA='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inputs():
 assert sha(INPUTS/'sites215.json')==SOURCE_SHA
 assert sha(INPUTS/'k215.native.tm')==TABLE_SHA
 rows=json.loads((INPUTS/'sites215.json').read_text())
 leaves={p:(op,a) for p,op,a in rows}
 assert len(leaves)==len(rows)
 @lru_cache(None)
 def tree(p):return leaves[p] if p in leaves else (tree(p+'0'),tree(p+'1'))
 T={}
 for line in (INPUTS/'k215.native.tm').read_text().splitlines():
  if line.startswith('#') or not line:continue
  q,b,w,d,z=line.split();assert (int(q),int(b)) not in T
  T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return rows,tree(''),T

def build():
 rows,root,T=inputs();ids={};nodes=[]
 def intern(n):
  if n in ids:return ids[n]
  data=list(n) if isinstance(n[0],str) else [intern(n[0]),intern(n[1])]
  ids[n]=len(nodes);nodes.append(data);return ids[n]
 root_id=intern(root);roles={};edges={};visits=[];lengths=Counter();traces=set();maxback=0
 def local(q,suffix,bit):
  tape={i-len(suffix):int(v)for i,v in enumerate(suffix)};tape[0]=bit
  before=tape.copy();h=0;trace=[]
  for tick in range(16):
   if h==1:return q,trace
   assert h in tape,('read outside explicit suffix',q,h,suffix,bit)
   w,d,z=T[q,tape[h]];trace.append([q,h,tape[h],w,d,z]);tape[h]=w;h+=d;q=z
   if h==1:assert tape==before,('changed prefix',suffix,bit)
  raise AssertionError('internal decoder block exceeds16 steps')
 def visit(n,p,q):
  nonlocal maxback
  suffix=('1'+p)[-2:];key=(ids[n],q,suffix)
  if key not in roles:roles[key]=len(roles)
  rid=roles[key];visits.append((p,ids[n],q));new_edges=[]
  for bit in (0,1):
   ch=n[bit]
   if isinstance(ch[0],str):
    new_edges.append({'kind':'primitive','node':ids[ch],'action':list(T[q,bit])})
   else:
    z,tr=local(q,suffix,bit);lengths[len(tr)]+=1;traces.add(tuple(map(tuple,tr)))
    maxback=max(maxback,-min(x[1]for x in tr))
    child=visit(ch,p+str(bit),z)
    new_edges.append({'kind':'internal','role':child,'steps':len(tr)})
  if rid in edges:assert edges[rid]==new_edges,('nonuniform context role',key)
  else:edges[rid]=new_edges
  return rid
 root_role=visit(root,'',84)
 result={'format':'two-bit-decoder-v1','parent_sha256':TABLE_SHA,'source_sha256':SOURCE_SHA,
  'nodes':nodes,'source_root':root_id,'root_role':root_role,
  'roles':[{'node':n,'state':q,'suffix':s,'edges':edges[r]}for(n,q,s),r in sorted(roles.items(),key=lambda x:x[1])]}
 summary={'internal_occurrences':len(visits),'internal_tree_nodes':len(set(n for p,n,q in visits)),
  'internal_state_roles':len(set((n,q)for p,n,q in visits)),
  'context_roles_by_suffix_length':{str(k):len(set((n,q,('1'+p)[-k:] if k else '')for p,n,q in visits))for k in range(6)},
  'occurrence_step_histogram':dict(sorted(lengths.items())),
  'distinct_internal_traces':len(traces),'maximum_readback':maxback}
 return result,summary

def verify(cert):
 rows,root,T=inputs()
 assert cert['format']=='two-bit-decoder-v1'
 assert cert['parent_sha256']==TABLE_SHA and cert['source_sha256']==SOURCE_SHA
 nodes=cert['nodes'];roles=cert['roles'];expanded=[]
 assert isinstance(nodes,list) and isinstance(roles,list) and nodes and roles
 def valid_index(i,n):return type(i)is int and 0<=i<n
 assert valid_index(cert['source_root'],len(nodes))
 assert valid_index(cert['root_role'],len(roles))
 for i,n in enumerate(nodes):
  assert isinstance(n,list) and len(n)==2
  if isinstance(n[0],str):
   assert n[0] in ['CI','CD','CB','CC','CH']
   assert n[1]is None if n[0]=='CH' else type(n[1])is int and n[1]>=0
  else:assert all(type(j)is int and 0<=j<i for j in n)
 used_nodes=set()
 def expand(i,p):
  used_nodes.add(i)
  n=nodes[i]
  if isinstance(n[0],str):expanded.append([p,*n]);return
  expand(n[0],p+'0');expand(n[1],p+'1')
 expand(cert['source_root'],'');assert expanded==rows and len(used_nodes)==len(nodes)
 for r in roles:
  assert valid_index(r['node'],len(nodes)) and type(r['state'])is int
  assert (r['state'],0)in T and (r['state'],1)in T
  assert isinstance(r['suffix'],str) and 1<=len(r['suffix'])<=2 and set(r['suffix'])<={'0','1'}
  assert isinstance(r['edges'],list) and len(r['edges'])==2
  for e in r['edges']:
   assert isinstance(e,dict)
   if e['kind']=='primitive':
    assert valid_index(e['node'],len(nodes))
    assert isinstance(e['action'],list) and len(e['action'])==3 and all(type(v)is int for v in e['action'])
   else:
    assert e['kind']=='internal' and valid_index(e['role'],len(roles)) and type(e['steps'])is int
 rr=roles[cert['root_role']]
 assert (rr['node'],rr['state'],rr['suffix'])==(cert['source_root'],84,'1')
 assert len({(r['node'],r['state'],r['suffix'])for r in roles})==len(roles)
 internal=primitive=max_steps=0;primitive_signatures=set();reachable={cert['root_role']};todo=list(reachable)
 for rid in todo:
  role=roles[rid];n=nodes[role['node']];q=role['state'];suffix=role['suffix']
  assert not isinstance(n[0],str) and len(role['edges'])==2
  assert 1<=len(suffix)<=2 and set(suffix)<={'0','1'}
  for bit,e in enumerate(role['edges']):
   child=nodes[n[bit]]
   if e['kind']=='primitive':
    assert isinstance(child[0],str) and e['node']==n[bit] and tuple(e['action'])==T[q,bit]
    primitive+=1;primitive_signatures.add((q,bit,*child,*e['action']));continue
   assert e['kind']=='internal' and not isinstance(child[0],str)
   target=roles[e['role']]
   assert target['node']==n[bit] and target['suffix']==(suffix+str(bit))[-2:]
   tape={j-len(suffix):int(v)for j,v in enumerate(suffix)};tape[0]=bit
   original=tape.copy();head=0;state=q
   assert 1<=e['steps']<=7
   for tick in range(e['steps']):
    assert head!=1 and head in tape
    write,move,state=T[state,tape[head]];tape[head]=write;head+=move
   assert (head,state,tape)==(1,target['state'],original)
   internal+=1;max_steps=max(max_steps,e['steps'])
   if e['role'] not in reachable:reachable.add(e['role']);todo.append(e['role'])
 assert len(reachable)==len(roles)
 return {'status':'PASS_INTERNAL_DECODER_AND_PRIMITIVE_ENTRY_BINDING',
  'scope':'Whole-tape internal traversal follows by finite local framing and induction on the source path. Primitive execution and the endpoint are separate obligations.',
  'source_nodes':len(nodes),'expanded_leaves':len(rows),'roles':len(roles),
  'internal_edge_rules':internal,'primitive_entry_rules':primitive,
  'distinct_primitive_entry_signatures':len(primitive_signatures),'maximum_internal_steps':max_steps,
  'source_sha256':SOURCE_SHA,'parent_sha256':TABLE_SHA}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',type=Path);ap.add_argument('--certificate',type=Path,default=ROOT/'evidence/decoder_context_certificate.json');args=ap.parse_args()
 if args.write:
  cert,summary=build();args.write.write_text(json.dumps(cert,separators=(',',':'))+'\n')
 else:
  cert=json.loads(args.certificate.read_text());_,summary=build()
 answer=verify(cert);answer.update(summary)
 answer['statistics_scope']='Role/rule counts are checked from the supplied certificate; occurrence/context histograms are regenerated source audits from the pinned inputs.'
 print(json.dumps(answer,indent=2))
if __name__=='__main__':main()
