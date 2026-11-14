#!/usr/bin/env python3
"""Densify the integrated-gate candidate and replay its full blank startup."""
from pathlib import Path
import json,hashlib
from check_raw_startup import load,check
from verify_renaming import verify
from compare_designs import canonical,read

BASE=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
TABLE=BASE/'math_reduction/folding/integrated_best_815732.tm'
SITES=BASE/'math_reduction/folding/integrated_best_815732.sites.json'

def main():
 m=load(TABLE);sites=json.loads(SITES.read_text());states=sorted({q for q,b in m});halts={z for w,d,z in m.values()}-set(states)
 if halts!={196}:raise ValueError(('halt labels',halts))
 low=[q for q in states if q<134];high=[q for q in states if q>=134]
 if low!=list(range(134))or len(high)!=69:raise ValueError(('unexpected state domain',low,high))
 mapping={q:q for q in low}|{q:134+i for i,q in enumerate(high)}|{196:203}
 if len(mapping)!=204 or len(set(mapping.values()))!=204:raise ValueError('map collision')
 nm={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in m.items()}
 target=OUT/'integrated_gate203_dense.tm';source=OUT/'integrated_gate203_sites.json'
 target.write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(nm.items())))
 source.write_text(json.dumps(sites)+'\n')
 conj=verify(TABLE,target,mapping)
 seen={0};todo=[0]
 while todo:
  q=todo.pop()
  for b in(0,1):
   if(q,b)in nm:
    z=nm[q,b][2]
    if z not in seen:seen.add(z);todo.append(z)
 receipt={'input_file':str(TABLE.relative_to(BASE)),'input_sha256':hashlib.sha256(TABLE.read_bytes()).hexdigest(),'input_sites_sha256':hashlib.sha256(SITES.read_bytes()).hexdigest(),'working_states':203,'rows':406,'source_sites':len(sites),'maximum_path':max(len(p)for p,op in sites),'dense_table':target.name,'dense_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'conjugacy':conj,'graph_reachable_working_states':len(seen-{203}),'unreachable_working_states':sorted(set(range(203))-seen),'mapping':mapping}
 print(json.dumps({k:v for k,v in receipt.items()if k!='mapping'},indent=2),flush=True)
 try:
  raw=check(TABLE,SITES,budget=1000000);dense=check(target,source,budget=1000000)
  for k in['steps','head','root','relative_ones','site25_path']:
   if raw[k]!=dense[k]:raise ValueError(('startup relabeling mismatch',k))
  receipt.update(status='PASS',raw_startup=raw,dense_startup=dense)
  print('EXACT STARTUP',raw['steps'],'head',raw['head'],'root visits',raw['root_visits'],flush=True)
 except ValueError as exc:
  receipt.update(status='STARTUP_FAILED',failure=str(exc));print('STARTUP FAILED',str(exc),flush=True)
 if not receipt['unreachable_working_states']:
  receipt['canonical_sha256']=canonical(*read(target))[0]
 (OUT/'integrated_gate203_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
