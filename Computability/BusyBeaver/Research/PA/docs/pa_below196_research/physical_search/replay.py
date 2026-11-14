#!/usr/bin/env python3
"""Reproduce bounded local searches; Python 3 and a C++17 compiler required.

These are finite simulation-certificate searches, not end-to-end PA proofs.
The default run replays seven-cell/two-row and displaced/one-row screens.
Pass --shared-three for the much larger complete-three-row shared-row subset.
"""
from __future__ import annotations
import argparse
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SHA = 'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
EXPECTED_WIDE = dict(pairs=38220, plain=0, first_keys=125092,
    first_patches=98072128, one=0, second_keys=1018338,
    second_patches=798376992, passes=0)
EXPECTED_OFFSET = dict(pairs=33735, plain=0, keys=47684,
    patches=37384256, passes=0)

def need(condition, message):
    if not condition:
        raise ValueError(message)

def parse(path):
    raw = path.read_bytes()
    need(hashlib.sha256(raw).hexdigest() == SHA, 'PA196 table hash changed')
    table = {}
    for line in raw.decode('ascii').splitlines():
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        need((q,b) not in table and b in (0,1) and w in (0,1)
             and d in ('L','R') and 0 <= t <= 196, 'Malformed transition')
        table[q,b] = w, 1 if d == 'R' else -1, t
    need(set(table) == {(q,b) for q in range(196) for b in (0,1)}, 'Domain mismatch')
    return table

def closure(table, radius=6):
    mask = (1 << (2*radius+1))-1
    initial = (0,0)
    seen = {initial}
    work = deque([initial])
    halt = False
    while work:
        q, bits = work.popleft()
        w, d, t = table[q,(bits >> radius)&1]
        if t == 196:
            halt = True
            continue
        bits = (bits & ~(1 << radius)) | (w << radius)
        for edge in (0,1):
            moved = ((bits >> 1) | (edge << (2*radius))) if d == 1 else ((bits << 1) | edge) & mask
            pair = t, moved
            if pair not in seen:
                seen.add(pair)
                work.append(pair)
    # A separate closure audit, not just trust in queue traversal.
    need(initial in seen, 'Initial abstract configuration missing')
    for q, bits in seen:
        w, d, t = table[q,(bits >> radius)&1]
        if t == 196:
            continue
        bits = (bits & ~(1 << radius)) | (w << radius)
        for edge in (0,1):
            moved = ((bits >> 1) | (edge << (2*radius))) if d == 1 else ((bits << 1) | edge) & mask
            need((t,moved) in seen, 'Window invariant is not closed')
    return seen, halt

def context_text(seen, active, radius=6):
    pairs = sorted({(q,(m >> (radius-active)) & ((1 << (2*active+1))-1)) for q,m in seen})
    if active == 2:
        pairs.sort(key=lambda x: (x[0], (x[1] >> active) & 1, x[1]))
    return ''.join(f'{q} {(m >> active)&1} {m}\n' for q,m in pairs), len(pairs)

def counts(text):
    w = text.split()
    need(len(w)%2 == 0, 'Bad search output')
    return dict(zip(w[::2],map(int,w[1::2])))

def execute(binary, table, contexts, output, n, *extra):
    r = subprocess.run([str(binary),str(table),str(contexts),str(output),str(n),*map(str,extra)],
                       check=True, capture_output=True, text=True)
    return counts(r.stdout), output.read_text()

def independent_controls():
    """Check both known positive witnesses by independent literal execution."""
    table = {(0,0):(1,-1,0),(0,1):(0,-1,3),(1,0):(0,-1,3),(1,1):(1,-1,2),
             (2,0):(1,-1,1),(2,1):(1,-1,2),(3,0):(0,1,2),(3,1):(1,1,2)}
    patches={(0,0):(1,-1,1),(1,1):(1,-1,3)}
    def project(q): return 0 if q == 2 else q
    for q in range(4):
        for mask in range(128):
            bits={p:(mask>>(p+3))&1 for p in range(-3,4)}
            old=bits.copy();w,d,t=table[q,bits[0]];old[0]=w
            goal=(project(t),d,old)
            state,head=project(q),0
            for _ in range(32):
                need(head in bits and state < 4,'Control escaped before endpoint')
                w,d,t=patches.get((state,bits[head]),table[state,bits[head]])
                bits[head]=w;state,head=project(t),head+d
                if (state,head,bits)==goal: break
            else: raise ValueError('Two-row control failed')
    # Five working controls; p=2 is identified with q=0 at head offset -2.
    target={0:1,1:3,2:5,3:5,4:2}
    for q in range(5):
        for mask in range(32):
            bits={p:(mask>>(p+2))&1 for p in range(-2,3)}
            state,head=(0,-2) if q == 2 else (q,0)
            t=target[q];goal=(0 if t==2 else t, -1 if t==2 else 1,bits.copy())
            for _ in range(32):
                need(head in bits and state<5,'Displaced control escaped')
                t=target[state];d=-1 if t==2 else 1;state=0 if t==2 else t;head+=d
                if (state,head,bits)==goal: break
            else: raise ValueError('Displaced control failed')
    return {'two_row_seven_cell_cases':4*128,'displaced_five_cell_cases':5*32}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('--output',type=Path,default=HERE/'replay_receipt.json')
    ap.add_argument('--shared-three',action='store_true')
    ap.add_argument('--workers',type=int,default=4)
    args=ap.parse_args()
    table=parse(args.table.resolve());seen,halt=closure(table)
    need(len(seen)==270067 and halt,'Abstract closure changed')
    controls=independent_controls()
    result={'input_sha256':SHA,'closure_radius':6,'closure_windows':len(seen),
            'abstract_halt_reachable':halt,'independent_controls':controls}
    with tempfile.TemporaryDirectory(prefix='pa196-local-search-') as td:
        temp=Path(td);binaries={}
        for mode,source in [('wide','scan_wide.cpp'),('offset','scan_offset.cpp'),('three','scan_three.cpp')]:
            binary=temp/mode
            subprocess.run(['g++','-O3','-std=c++17',str(HERE/source),'-o',str(binary)],check=True)
            binaries[mode]=binary
        # The optimized engines must also recover the independently checked witnesses.
        ct=temp/'control.tm'
        ct.write_text('0 0 1 L 0\n0 1 0 L 3\n1 0 0 L 3\n1 1 1 L 2\n2 0 1 L 1\n2 1 1 L 2\n3 0 0 R 2\n3 1 1 R 2\n')
        cc=temp/'control_contexts.txt'
        cc.write_text(''.join(f'{q} {(m>>3)&1} {m}\n' for q in range(4) for m in range(128)))
        c,w=execute(binaries['wide'],ct,cc,temp/'control_wide.out',4,2,0)
        need(w.strip()=='PASS 2 0 0 1 -1 1 3 1 -1 3' and c['passes']==1,'Wide engine control failed')
        result['synthetic_wide_engine']=c
        cc.write_text(''.join(f'{q} {(m>>2)&1} {m}\n' for q in range(4) for m in range(32)))
        c,w=execute(binaries['three'],ct,cc,temp/'control_three.out',4,2,0)
        need(w.strip()=='PASS 2 0 0 1 -1 1 3 1 -1 3' and c['found']==1,'Three-row engine control failed')
        result['synthetic_three_engine']=c
        target={0:1,1:3,2:5,3:5,4:2}
        ct.write_text(''.join(f'{q} {b} {b} R {n}\n' for q,n in target.items() for b in (0,1)))
        cc.write_text(''.join(f'{q} {(m>>2)&1} {m}\n' for q in range(5) for m in range(32)))
        c,w=execute(binaries['offset'],ct,cc,temp/'control_offset.out',5,2)
        need(w.strip()=='PLAIN 2 0 -2' and c['plain']==1,'Displaced engine control failed')
        result['synthetic_offset_engine']=c
        files={}
        for active in (2,3,6):
            txt,n=context_text(seen,active);files[active]=temp/f'contexts{active}.txt';files[active].write_text(txt)
            result[f'contexts_radius{active}']={'count':n,'sha256':hashlib.sha256(txt.encode()).hexdigest()}
        table_path=args.table.resolve()
        c,w=execute(binaries['wide'],table_path,files[3],temp/'wide.out',196)
        need(c==EXPECTED_WIDE and not w,'Seven-cell search results changed')
        result['wide']={'active_radius':3,'max_child_steps':32,'max_changed_rows':2,'counts':c}
        c,w=execute(binaries['offset'],table_path,files[6],temp/'offset.out',196,6)
        need(c==EXPECTED_OFFSET and not w,'Displaced search results changed')
        result['offset']={'active_radius':6,'max_child_steps':32,'max_additional_changed_rows':1,'offsets':[-2,2],'counts':c}
        if args.shared_three:
            pairs=[(a,b) for a in range(196) for b in range(196) if a!=b and any(table[a,i]==table[b,i] for i in (0,1))]
            need(len(pairs)==348,'Shared-row pair list changed')
            def one(pair):
                a,b=pair;c,w=execute(binaries['three'],table_path,files[2],temp/f'three_{a}_{b}.out',196,a,b)
                return {'drop':a,'keep':b,'counts':c,'survivors':w.splitlines()}
            with ThreadPoolExecutor(max_workers=args.workers) as pool:
                rows=list(pool.map(one,pairs))
            result['shared_three']={'active_radius':2,'max_child_steps':16,'max_changed_rows':3,'pairs':rows}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':
    main()
