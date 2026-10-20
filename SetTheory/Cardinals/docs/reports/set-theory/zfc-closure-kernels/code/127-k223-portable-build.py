#!/usr/bin/env python3
"""Deterministically build the conditional-K 223-state transition table.

Standard library only. Source/theory calibration and universal instruction
correctness are separate proof obligations; this script checks the literal
construction, state census, canonical relabeling, and all-tape local fold.
"""
from pathlib import Path
import argparse,hashlib,json
import verify_state_fold as fold
from reconstruct_source import reconstruct
HERE=Path(__file__).resolve().parent
EXPECTED_CANONICAL='7edafbb2395d39e3b0895a5e0f4da61e12a371b0af71ef4cfb1a43c06e7b917f'
def require(p,m):
 if not p:raise ValueError(m)
def digest(data):return hashlib.sha256(data).hexdigest()
def encode(t,start):return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def write_json(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
def canonical(t,start):
 order=[start];mp={start:0}
 for q in order:
  for b in(0,1):
   z=t[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(order);order.append(z)
 require(set(order)=={q for q,b in t},'Unreachable working state');mp[254]=len(order)
 return {(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()},mp

def source_census(data):
 rows=json.loads(data);leaves={p:(op,arg)for p,op,arg in rows};require(len(leaves)==len(rows),'Duplicate source leaf')
 seen=set();zero=depth=0;visited=[]
 def rec(p=''):
  nonlocal zero,depth
  if p in leaves:
   op,arg=leaves[p];require(op in('CI','CD','CC','CB','CH'),'Unknown operation');require((arg is None)if op=='CH'else isinstance(arg,int),'Malformed argument');visited.append([p,op,arg]);depth=max(depth,len(p));zero=max(zero,max(map(len,p.split('1'))));node=(op,arg)
  else:
   require(len(p)<100,'Incomplete binary source');node=(rec(p+'0'),rec(p+'1'))
  seen.add(node);return node
 rec();require(visited==rows,'Source not in exact binary traversal order')
 return dict(distinct_source_nodes=len(seen),leaf_instructions=len(rows),guarded_cases=len(rows)+sum(op=='CD'for p,op,arg in rows),maximum_depth=depth,maximum_zero_run=zero)

def build(out):
 recipe=json.loads((HERE/'recipe.json').read_text());inputs=HERE/'inputs'
 for name,sha in recipe['input_sha256'].items():require(digest((inputs/name).read_bytes())==sha,f'Changed pinned input {name}')
 old,st=fold.table(inputs/'baseline224.k.tm');require(st==0 and len(old)==448,'Wrong input224 table')
 pre=old.copy()
 for edit in recipe['allocation_patch']:
  key=(edit['state'],edit['read']);want=tuple(edit['old'])if edit['old']is not None else None;require(pre.get(key)==want,f'Allocation patch precondition failed at {key}')
  if edit['new']is None:pre.pop(key)
  else:pre[key]=tuple(edit['new'])
 predata=encode(pre,st);require(digest(predata)==recipe['prefold_sha256'],'Prefold224 checksum mismatch');fold.parse_table(predata);require(len(pre)==448,'Wrong prefold224 census')
 f=recipe['fold'];keep,drop=f['keep'],f['drop'];phi=lambda q:keep if q==drop else q
 new={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in pre.items()if q!=drop}
 for bit,action in f['rows'].items():new[keep,int(bit)]=tuple(action)
 data=encode(new,st);require(digest(data)==recipe['candidate_sha256'],'Candidate223 checksum mismatch');fold.parse_table(data);require(len(new)==446,'Wrong final223 census')
 proof=fold.prove(pre,new,st,st,keep,drop,0,None,8,65,20000);require(proof['status']=='PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION','Local all-tape fold proof failed')
 canon,mp=canonical(new,st);canonical_data=encode(canon,mp[st]);require(digest(canonical_data)==EXPECTED_CANONICAL,'Canonical223 checksum mismatch');require(mp[254]==223 and mp[84]==22,'Unexpected canonical interface')
 rawmap=json.loads((inputs/'legacy_state_map.json').read_text())['k230_to_old'];lm={q:int(rawmap[str(q)])for q,b in new};lm[254]=254;require(len(lm)==len(set(lm.values())),'Noninjective legacy map')
 legacy={(lm[q],b):(w,d,lm[z])for(q,b),(w,d,z)in new.items()};sites=reconstruct(inputs);require(sites==(inputs/'sites.json').read_bytes(),'Pinned source descriptor differs');census=source_census(sites)
 require(census==dict(distinct_source_nodes=210,leaf_instructions=4799,guarded_cases=6238,maximum_depth=38,maximum_zero_run=6),'Changed source census')
 out.mkdir(parents=True,exist_ok=True)
 artifacts={'prefold224.k.tm':predata,'candidate223.k.tm':data,'candidate223.tm':canonical_data,'candidate223.legacy.tm':encode(legacy,lm[st]),'sites.json':sites}
 for name,blob in artifacts.items():(out/name).write_bytes(blob)
 write_json(out/'local_fold_proof.json',proof);write_json(out/'renumbering223.json',dict(native_to_canonical=mp,canonical_to_native={v:k for k,v in mp.items()},native_to_legacy=lm))
 result=dict(status='EXACT_223_CONSTRUCTION_AND_LOCAL_FOLD_PASS',working_states=223,rows=446,all_working_states_graph_reachable=True,native=dict(start=0,dispatcher=84,halt=254),canonical=dict(start=0,dispatcher=22,halt=223),canonicalization='Breadth-first discovery from native0; read0 before read1; halt last.',allocation_patch_rows=len(recipe['allocation_patch']),source=census,artifacts={n:digest(v)for n,v in artifacts.items()},scope='Literal construction, census, canonical isomorphism and all-tape positive-block proof of final fold. Complete blank startup, unbounded instruction correctness, source/emitter calibration and logical equiconsistency require their separate certificates.')
 write_json(out/'construction223.json',result);return result
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE/'results');a=ap.parse_args();print(json.dumps(build(a.output),indent=2,sort_keys=True))
