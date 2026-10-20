#!/usr/bin/env python3
"""Exact table census, bijective canonical labeling and two full startup interpreters."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys
from construct import ROOT,sha,dump,read_table,table_bytes
PHY=(6,2,0,4,3,7,8,5,1)
def startup(table,sites,steps,out,th,sh):
    states={q for q,b in table}; assert len(states)==219 and len(table)==438
    assert set(table)=={(q,b) for q in states for b in (0,1)}
    assert {z for w,d,z in table.values()}-states=={254}
    assert 254 not in states
    order=[0]; mp={0:0}
    for q in order:
        for b in (0,1):
            z=table[q,b][2]
            if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
    assert set(mp)==states;mp[254]=219
    dense_table={(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in table.items()}
    data='#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(dense_table.items()))
    (out/'k219.tm').write_text(data)
    ones=set();q=h=0;visits=Counter()
    for _ in range(steps):
        b=int(h in ones);visits[q,b]+=1;w,d,q=table[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    tape=bytearray(2*steps+3); origin=steps+1; head=origin; state=0; dv=Counter()
    for _ in range(steps):
        b=tape[head];dv[state,b]+=1;w,d,state=dense_table[state,b];tape[head]=w;head+=d
    logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=logical[i]
    expected={-6,139};pos=140
    for v in physical+[1]*130:
        pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
    assert (q,h,ones)==(84,-5,expected)
    assert (state,head-origin,{i-origin for i,v in enumerate(tape) if v})==(mp[84],-5,expected)
    assert dv==Counter({(mp[q],b):v for (q,b),v in visits.items()})
    result=dict(status='INDEPENDENT_EXACT_TABLE_STARTUP_CENSUS_PASS',table_sha256=th,source_sha256=sh,
        states=219,rows=438,start=0,dispatch=84,halt=254,all_states_graph_reachable=True,
        canonical_sha256=sha(out/'k219.tm'),native_to_canonical=mp,
        startup=dict(steps=steps,state=q,head=h,ones=sorted(ones),all_other_cells=0,logical_registers=logical,
        physical_registers=physical,spares=[1]*130,header=139,extra_gap=80,sparse_and_dense_agree=True))
    dump(out/'canonicalization.json',result)
    return result


if __name__=='__main__':
    assert __debug__ and not sys.flags.optimize
    ap=argparse.ArgumentParser();ap.add_argument('--variant',required=True);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    rec=json.loads((ROOT/'machine/construction.json').read_text())['variants'][a.variant]
    assert sha(a.table)==rec['native_sha256'] and sha(a.source)==rec['source_sha256']
    t=read_table(a.table);a.output.mkdir(parents=True,exist_ok=True)
    signed={(q,b):(w,1 if d=='R' else -1,z)for(q,b),(w,d,z)in t.items()}
    result=startup(signed,json.loads(a.source.read_text()),rec['startup_steps'],a.output,sha(a.table),sha(a.source))
    mp={102:301,120:302}
    upstream={(mp.get(q,q),b):(w,d,mp.get(z,z))for(q,b),(w,d,z)in t.items()}
    (a.output/'k219.upstream-labels.tm').write_bytes(table_bytes(upstream))
    result.update(release_native_labeling='search labels102/120, start0, dispatch84, halt254',upstream_label_map=mp,upstream_labels_sha256=sha(a.output/'k219.upstream-labels.tm'))
    dump(a.output/'canonicalization.json',result)
    print(result['status'])
