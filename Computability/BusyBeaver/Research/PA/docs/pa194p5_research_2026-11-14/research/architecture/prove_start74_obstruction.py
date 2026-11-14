#!/usr/bin/env python3
"""Nine complete traces certify the start-74 obstruction for all router permutations.

Only a source-instruction entry edge targeting a register scanner may change.
The nine scan-state rows themselves are fixed. These are literal finite-prefix
certificates followed by a mathematically certified outward self-loop.
"""
from pathlib import Path
import argparse, hashlib, json

P = Path(__file__).resolve().parent
DEFAULT = P / 'runtime193.native.tm'
SK = [51,36,25,48,32,33,22,55,60]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',nargs='?',type=Path,default=DEFAULT);args=ap.parse_args()
    data=args.table.read_bytes()
    assert hashlib.sha256(data).hexdigest()=='50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53'
    rows={(int(q),int(b)):(int(w),1 if d=='R' else -1,int(n))for q,b,w,d,n in map(str.split,data.decode().splitlines())}
    # These are the complete sites where a source operation enters a scanner.
    routers={(q,b)for(q,b),(w,d,n)in rows.items()if b==1 and w==0 and d==1 and n in SK and q not in SK}
    cases=[]
    for target in SK:
        table=dict(rows);table[45,1]=(0,1,target)
        q,h,ones=74,0,set();trace=[];used=[]
        for step in range(200):
            b=int(h in ones)
            if(q,b)in routers:used.append([step,q,b])
            if q==35 and b==0 and h>max(ones,default=h-1):break
            w,d,n=table[q,b];trace.append([q,h,b,w,d,n]);(ones.add if w else ones.discard)(h);q,h=n,h+d
        else:raise AssertionError('No ray')
        assert used==[[78,45,1]],used
        assert table[35,0]==(1,1,35) and ones=={-3,1}
        cases.append(dict(scanner_target=target,steps=step,state=q,head=h,ones=sorted(ones),router_edges_used=used,trace=trace))
    common=cases[0]['trace'][:78]
    assert all(c['trace'][:78]==common for c in cases)
    result=dict(input_sha256=hashlib.sha256(data).hexdigest(),working_states=193,scan_states=SK,
        scope='All permutations of source-instruction router targets into the nine fixed scanners; fixed start74 and other rows unchanged.',
        common_prefix_length=78,cases=cases,
        conclusion='Each case reaches state35 to the right of all one-cells; 35/0=1R35 proves an outward ray by induction.')
    (P/'start74_permutation_obstruction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='cases'},indent=2))
    print(json.dumps([{k:v for k,v in c.items()if k!='trace'}for c in cases],indent=2))

if __name__=='__main__':main()
