#!/usr/bin/env python3
"""Replay an explicit transition recipe; Python standard library only."""
from pathlib import Path
import argparse,json,hashlib

def main():
 ap=argparse.ArgumentParser();ap.add_argument('baseline',type=Path);ap.add_argument('recipe',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args();r=json.loads(a.recipe.read_text());assert r['format']=='native-transition-delta-v1';assert hashlib.sha256(a.baseline.read_bytes()).hexdigest()==r['baseline_sha256'];T={}
 for line in a.baseline.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=int(q),int(b);assert key not in T;T[key]=int(w),1 if d=='R'else-1,int(z)
 T={k:v for k,v in T.items()if k[0]not in r['remove_states']}
 for q,b,w,d,z in r['replace_or_add_rows']:T[q,b]=(w,d,z)
 states={q for q,b in T};assert len(T)==2*len(states)==2*r['working_states'];assert all((q,b)in T for q in states for b in(0,1));assert {z for w,d,z in T.values()}-states=={r['halt']};assert r['start']in states
 raw=('#! start '+str(r['start'])+'\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode();assert hashlib.sha256(raw).hexdigest()==r['output_sha256'];a.output.write_bytes(raw);print('EXACT_RECONSTRUCTION_PASS',len(states),'working states')
if __name__=='__main__':main()
