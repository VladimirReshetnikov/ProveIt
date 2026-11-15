#!/usr/bin/env python3
"""Reconstruct PA194-LCSF3 from its literal, SHA-pinned LC_AX11H_SF parent."""
import argparse, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'reference/composites/machines/PA194LC_AX11H_SF'
EXPECTED_PARENT='23c40299b43056202f3f9bbe562e52f35b23dc25c13e0cb5e4f556444d86d0a5'
EXPECTED_NATIVE='b741261b92a17256dfcbc9c6d3ee38d4fb27a3eee9be180a54ca63dca1c13cfe'
EXPECTED_DENSE='2e5684567cd6e6e59fd99b5b093071533bcef6a01012dd2c6e41d52c645d2768'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    t={}
    for line in p.read_text().splitlines():
        q,b,w,d,n=line.split(); k=(int(q),int(b)); assert k not in t
        t[k]=(int(w),d,int(n))
    return t
def text(t):return ''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(t.items()))
def main():
    a=argparse.ArgumentParser();a.add_argument('--output',type=Path,default=ROOT/'candidate');args=a.parse_args()
    assert __debug__ and sha(PARENT/'machine.native.tm')==EXPECTED_PARENT
    old=read(PARENT/'machine.native.tm');new=dict(old)
    assert old[190,1]==(1,'L',73);new[190,1]=(0,'L',42)
    labels=json.loads((PARENT/'labels.json').read_text());inv={q:i for i,q in enumerate(labels)}
    assert len(labels)==195 and labels[0]==74 and labels[-1]==254
    dense={(inv[q],b):(w,d,inv[n]) for (q,b),(w,d,n) in new.items()}
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    (out/'machine.native.tm').write_text(text(new));(out/'machine.tm').write_text(text(dense))
    (out/'labels.json').write_text(json.dumps(labels)+'\n')
    assert sha(out/'machine.native.tm')==EXPECTED_NATIVE
    assert sha(out/'machine.tm')==EXPECTED_DENSE
    result={'name':'PA194LCAX11HSF3','short_name':'PA194-LCSF3','states':194,'rows':388,'alphabet':[0,1],
        'dense_start':0,'dense_halt':194,'native_start':74,'native_halt':254,
        'parent_native_sha256':EXPECTED_PARENT,'native_sha256':EXPECTED_NATIVE,'dense_sha256':EXPECTED_DENSE,
        'native_edits':[[190,1,[1,'L',73],[0,'L',42]]],
        'dense_edits':[[116,1,[1,'L',37],[0,'L',48]]],
        'scope':'Relative iPRA theorem; inherited AX11H/LC/SF written consistency calibration; no completed Lean endpoint.'}
    (out/'construction.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
