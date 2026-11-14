#!/usr/bin/env python3
"""Independently check every row of a literal machine relabeling."""
from pathlib import Path
import argparse,json
from check_raw_startup import load

def verify(source,target,mapping):
 source=load(source);target=load(target);mapping={int(q):int(r)for q,r in mapping.items()};old={q for q,b in source};new={q for q,b in target};oldtargets={z for w,d,z in source.values()};newtargets={z for w,d,z in target.values()}
 if set(mapping)!=old|oldtargets:raise ValueError('map domain differs from complete state/halt domain')
 if len(set(mapping.values()))!=len(mapping):raise ValueError('map is not injective')
 if {mapping[q]for q in old}!=new or {mapping[q]for q in oldtargets}!=newtargets:raise ValueError('map range differs from target domain')
 for(q,b),(w,d,z)in source.items():
  if target.get((mapping[q],b))!=(w,d,mapping[z]):raise ValueError(('transition mismatch',q,b))
 if len(source)!=len(target):raise ValueError('row counts differ')
 return{'rows_checked':len(source),'working_states':len(old),'complete_conjugacy':True}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('target');p.add_argument('mapping_json');p.add_argument('--key',default='mapping');a=p.parse_args();data=json.loads(Path(a.mapping_json).read_text());print(json.dumps(verify(a.source,a.target,data[a.key]if a.key else data),indent=2))
