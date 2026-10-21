#!/usr/bin/env python3
"""Compare exact M124 and FM215 tables without conflating provider choices."""
import argparse, hashlib, json
from pathlib import Path

def read_table(p):
    rows={}
    for line in p.read_text().splitlines():
        f=line.split()
        if len(f)==5 and f[0].isdigit() and f[1] in ('0','1') and f[2] in ('0','1') and f[3] in ('L','R') and f[4].isdigit():
            key=(int(f[0]),int(f[1]))
            assert key not in rows
            rows[key]=(int(f[2]),f[3],int(f[4]))
    states={q for q,b in rows}
    assert len(states)==215 and len(rows)==430
    assert all((q,b) in rows for q in states for b in [0,1])
    assert all(q in states or q==254 for _,_,q in rows.values())
    return rows

def canonical(t, reflect=False):
    labels={0:0}; queue=[0]; out=[]
    for q in queue:
        for b in [0,1]:
            w,d,r=t[q,b]
            if r==254: nr='HALT'
            else:
                if r not in labels: labels[r]=len(labels); queue.append(r)
                nr=labels[r]
            if reflect: d={'L':'R','R':'L'}[d]
            out.append([labels[q],b,w,d,nr])
    assert len(queue)==215
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('m124',type=Path); ap.add_argument('fm215',type=Path)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args(); m=read_table(a.m124); f=read_table(a.fm215)
    diff=[{'state':q,'read':b,'M124':m[q,b],'FM215':f[q,b]} for q,b in sorted(m) if m[q,b]!=f[q,b]]
    assert diff==[{'state':127,'read':1,'M124':(1,'R',59),'FM215':(1,'R',109)}]
    result={'M124_sha256':hashlib.sha256(a.m124.read_bytes()).hexdigest(),
            'FM215_sha256':hashlib.sha256(a.fm215.read_bytes()).hexdigest(),
            'differences':diff,'rooted_isomorphic':canonical(m)==canonical(f),
            'rooted_reflection_isomorphic':canonical(m)==canonical(f,True),
            'provider_read0_equal':m[59,0]==m[109,0],
            'provider_read1_equal':m[59,1]==m[109,1],
            'working_states_each':215,'rows_each':430,
            'scope':'Rooted action-preserving transition-graph equality, also global L/R reflection; not arbitrary semantic equivalence.'}
    a.out.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
if __name__=='__main__': main()
