#!/usr/bin/env python3
"""Exact canonical/legacy conjugacy, complete sparse blank run, and table census.

This verifier is independent of the source constructor and dense initializer.
It reads a literal K-labelled table, regenerates the other serializations,
and checks the complete expected tape after 409835 transitions.
"""
from pathlib import Path
import argparse,csv,hashlib,json,sys

PINS={
 'conditional':dict(k='d1ad27580fb8ec41c183760e738a03b1651cc7e2bebc2d48a29a893ca8b34e40',
  canonical='60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1',
  legacy='4c231175d609fdfeb78c4aad8653cb0ca83ce929002dbff375ec4e8bccf8a57f'),
 'seed':dict(k='726583d188c22ee0d8572083a22497657c60e33fc80159d317767046dbbda365',
  canonical='3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476',
  legacy='e7d9e3ae06ad7afa9783f37d5f268ddf1bc9d5a297d88abeaee171b07f8d0a6a')}
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def read(raw):
 table={};starts=[]
 for line in raw.decode('ascii').splitlines():
  if line.startswith('#! start '):starts.append(int(line.split()[-1]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  need((q,b)not in table and b in(0,1) and w in(0,1) and d in('L','R'),'Bad row')
  table[q,b]=w,1 if d=='R' else -1,z
 states={q for q,b in table}
 need(starts==[0] and len(states)==222 and len(table)==444,'Bad census or start')
 need(set(table)=={(q,b)for q in states for b in(0,1)},'Partial table')
 need({z for w,d,z in table.values()}-states=={254},'Unexpected terminal target')
 return table
def encode(table,start=0):
 return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'
  for(q,b),(w,d,z)in sorted(table.items()))).encode('ascii')
def relabel(table,mapping):
 return {(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in table.items()}
def verify(table,raw,variant,legacy_map):
 pin=PINS[variant];need(sha(raw)==pin['k'],'Unexpected literal K table')
 order=[0];mapping={0:0}
 for q in order:
  for b in(0,1):
   z=table[q,b][2]
   if z!=254 and z not in mapping:mapping[z]=len(order);order.append(z)
 need(set(order)=={q for q,b in table},'Declared graph-unreachable states')
 mapping[254]=222;canonical=relabel(table,mapping)
 need(mapping[84]==22 and set(mapping.values())==set(range(223)),'Canonical labels')
 canonical_bytes=encode(canonical);need(sha(canonical_bytes)==pin['canonical'],'Canonical digest')
 old=json.loads(legacy_map.read_text())
 legacy={int(k):int(v)for k,v in old['k230_to_old'].items()};legacy[254]=254
 for q in mapping:
  if q not in legacy:legacy[q]=q+1000
 need(len({legacy[q]for q in mapping})==223,'Legacy labels collide')
 legacy_bytes=encode(relabel(table,legacy),legacy[0])
 need(sha(legacy_bytes)==pin['legacy'],'Legacy digest')
 # Sparse set represents every nonzero tape cell, with implicit zero exterior.
 q=0;h=0;ones=set()
 for step in range(409835):
  need(q!=254,'Premature halt during initialization')
  b=int(h in ones);w,d,q=table[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 need(q==84 and h==-5 and ones and min(ones)==-6,'Wrong startup state or marker')
 header=min(x for x in ones if x>=h);position=header+1;values=[]
 while position<=max(ones):
  need(position not in ones and position+1 in ones,'Malformed unary block')
  position+=1;begin=position
  while position in ones:position+=1
  values.append(position-begin-1)
 need(position==max(ones)+1,'Malformed tape suffix')
 need(header==176 and values==[0,0,0,3,0,0,3,0,0]+[1]*167,'Wrong register file')
 need(len(ones)==351,'Unexpected nonzero support')
 # Reconstruction from the decoded frame excludes all other nonzero cells.
 expected={-6,176};position=177
 for value in values:
  position+=1;expected.update(range(position,position+value+1));position+=value+1
 need(ones==expected,'Extraneous nonzero cell')
 receipt=dict(status='EXACT_MACHINE_CONJUGACY_AND_SPARSE_BOOTSTRAP_PASS',variant=variant,
  working_states=222,transition_rows=444,graph_reachable_states=222,start=0,halt=222,
  canonical_dispatcher=22,k_dispatcher=84,steps=409835,head=h,header=header,
  zero_gap=181,extra_gap=117,logical_registers=[3,0,0,0,3,0,0,0,0],
  physical_register_map=[6,2,0,4,3,7,8,5,1],spare_count=167,spare_values=1,
  one_cells=sorted(ones),all_unlisted_cells=0,sha256=pin,
  k_to_canonical=mapping,k_to_legacy={q:legacy[q]for q in mapping})
 return canonical,canonical_bytes,legacy_bytes,receipt
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--table',type=Path,required=True)
 ap.add_argument('--variant',choices=PINS,required=True)
 ap.add_argument('--legacy-map',type=Path,required=True)
 ap.add_argument('--output-dir',type=Path,required=True)
 a=ap.parse_args();need(__debug__ and not sys.flags.optimize,'Run without -O')
 raw=a.table.read_bytes();canonical,cb,lb,receipt=verify(read(raw),raw,a.variant,a.legacy_map)
 a.output_dir.mkdir(parents=True,exist_ok=True)
 (a.output_dir/'candidate222.tm').write_bytes(cb)
 (a.output_dir/'candidate.legacy.tm').write_bytes(lb)
 with(a.output_dir/'candidate222.csv').open('w',newline='')as f:
  out=csv.writer(f);out.writerow(['state','read','write','move','next'])
  out.writerows((q,b,w,'R'if d==1 else'L',z)for(q,b),(w,d,z)in sorted(canonical.items()))
 dump(a.output_dir/'machine_check.json',receipt)
 print(json.dumps({k:receipt[k]for k in('status','variant','working_states','transition_rows','steps','sha256')},indent=2))
if __name__=='__main__':main()
