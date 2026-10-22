#!/usr/bin/env python3
"""Independent list-of-bits inductive closure check for the saved invariant."""
import argparse,hashlib,json
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('invariant');ap.add_argument('--out',default='window_invariant_audit.json');a=ap.parse_args();T={}
    for line in Path(a.table).read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),d,int(z))
    raw=Path(a.invariant).read_bytes();I=json.loads(raw);r=I['radius'];masks={int(q):set(mm)for q,mm in I['masks'].items()};states=set(q for q,b in T)
    assert set(masks)==states and 0 in masks[0] and I['blank_window']
    assert all(0<=m<2**(2*r+1)for mm in masks.values()for m in mm)
    checked=0;halting=0
    for q,mm in masks.items():
        for mask in mm:
            word=[(mask//(2**i))%2 for i in range(2*r+1)];w,d,z=T[q,word[r]];word[r]=w
            if z not in states:
                assert z==215;halting+=1;continue
            for bit in [0,1]:
                nxt=word[1:]+[bit] if d=='R' else [bit]+word[:-1]
                encoded=sum(v*2**i for i,v in enumerate(nxt))
                assert encoded in masks[z],('Not closed',q,mask,w,d,z,bit);checked+=1
    count=sum(map(len,masks.values()));assert count==I['configs']
    result={'status':'INDUCTIVE_WINDOW_CLOSURE_PASS','radius':r,'initial_scope':'All-zero tape at control0; arbitrary entering exterior bits in the abstraction','configurations':count,'nonhalting_successor_obligations':checked,'halting_abstract_configurations':halting,'table_sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'invariant_sha256':hashlib.sha256(raw).hexdigest(),'auditor_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
