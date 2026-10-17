#!/usr/bin/env python3
"""Independently check a native window file's initial and closure obligations.

The checker validates the table against the pinned baseline, then validates
every listed abstract successor using a dense membership array. It does not
call or import the native fixed-point generator.
"""
from pathlib import Path
import argparse, hashlib, json, time
from reproduce import PACKAGE, table_input

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    assert __debug__
    begin=time.monotonic();rows=table_input(PACKAGE/'inputs/permutation252_old.tm')
    with a.input.open() as f:
        n,r,k=map(int,f.readline().split());assert n==252 and r in (6,8) and k==64
        for q in range(n):
            for b in (0,1):assert tuple(map(int,f.readline().split()))==rows[q,b]
        position=f.tell();width=2*r+1;patterns=1<<width;mask=patterns-1
        seen=bytearray((n+1)*patterns);count=0
        for q in range(n+1):
            size,*values=map(int,f.readline().split());assert size==len(values)
            assert values==sorted(set(values)) and all(0<=p<patterns for p in values)
            for p in values:seen[q*patterns+p]=1
            count+=size
        assert not f.read().strip();assert seen[0]==1
        f.seek(position);obligations=0
        for q in range(n+1):
            size,*values=map(int,f.readline().split())
            if q==n:continue
            for p in values:
                w,d,t=rows[q,(p>>r)&1];updated=(p&~(1<<r))|(w<<r)
                if d==1:base=updated>>1;extra=1<<(width-1)
                else:base=(updated<<1)&mask;extra=1
                assert seen[t*patterns+base] and seen[t*patterns+(base|extra)]
                obligations+=2
    result={'status':'PASS','radius':r,'state_window_pairs':count,'successor_obligations':obligations,'initial_included':True,'actual_table_matches':True,'input_sha256':hashlib.sha256(a.input.read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-begin,'scope':'Independent explicit finite invariant verification; all original blank runs covered by ordinary induction. No claim every admitted window is reachable.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
