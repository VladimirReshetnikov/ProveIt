#!/usr/bin/env python3
"""Independently replay the finite prefixes and check the outward-ray criterion."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent

def verify():
    reports=json.loads((ROOT/'results/rejected_hybrid193_startups.json').read_text())
    for report in reports:
        name={'ax11h':'AX11H194','qax11h':'QAX11H194'}[report['machine']]
        data=(ROOT/'inputs'/f'{name}.native.tm').read_bytes()
        assert hashlib.sha256(data).hexdigest()==report['input_native_sha256']
        table={}
        for line in data.decode().splitlines():
            q,b,w,d,n=line.split();table[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
        assert table[88,0]==(0,1,122) and table[301,0]==(0,1,45) and table[51,0]==(0,1,16)
        table={k:(w,d,88 if n==301 else n) for k,(w,d,n) in table.items() if k[0]!=301}
        table[88,0]=(0,-1,51);table[51,0]=(0,1,122)
        assert len(table)==386 and len({q for q,b in table})==193
        q,h,ones=74,0,set();cert=report['certificate']
        assert len(cert['trace'])==cert['steps']==92
        for row in cert['trace']:
            b=int(h in ones);w,d,n=table[q,b]
            assert row==[q,h,b,w,d,n]
            (ones.add if w else ones.discard)(h);q,h=n,h+d
        assert (q,h,sorted(ones))==(cert['q'],cert['head'],cert['ones'])==(35,14,[-3,1])
        assert cert['status']=='RAY' and table[q,0]==(1,1,q) and h>max(ones)
        # The last assertion is the finite hypothesis of the induction:
        # at each next step the head is strictly beyond previous support,
        # writes one there, and moves right in the same control.
        print(name,'PASS: 92-step prefix followed by an outward ray')
    return len(reports)
if __name__=='__main__':verify()
