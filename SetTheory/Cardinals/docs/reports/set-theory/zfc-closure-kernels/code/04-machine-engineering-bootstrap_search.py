#!/usr/bin/env python3
"""Search existing blank start states after deleting the shared initializer.

Only finite executions and exact finite cycles are reported. A fuel limit
never constitutes a nontermination or invalidity proof.
"""
from pathlib import Path
from collections import Counter
import argparse
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze_table import parse_table


def patched(baseline):
    rows, _, _, _, sha = parse_table(baseline)
    assert sha == 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
    rows.update({(3,0):(0,'L',48), (5,0):(1,'R',97), (5,1):(1,'R',64), (49,1):(0,'R',5)})
    return {k:(w,d,64 if t == 5 else t) for k,(w,d,t) in rows.items() if k[0] not in (5,8)}


def frame(tape, head):
    if head-1 not in tape or any(p < head-1 for p in tape):
        return None
    ones = sorted(p-head for p in tape if p >= head)
    headers = [p for p in ones if p >= 34]
    if not headers:
        return None
    header = headers[0]
    if header < 40:
        return None
    pc = ''.join('1' if head+i in tape else '0' for i in range(34)).rstrip('0')
    x = head + header + 1
    regs = []
    while x not in tape and x+1 in tape:
        x += 1
        n = 0
        while x in tape:
            n += 1
            x += 1
        regs.append(n-1)
    if len(regs) < 9 or any(p >= x for p in tape):
        return None
    physical_to_source = (2,4,3,7,6,8,0,1,5)
    source = [0]*9
    for j,r in enumerate(physical_to_source):
        source[r] = regs[j]
    return {'pc':pc, 'gap':header, 'source_regs':source, 'spare_blocks':len(regs)-9, 'spare_nonzero':[(j,v) for j,v in enumerate(regs[9:]) if v]}


def simulate(rows, start, fuel):
    q,h,tape = start,0,set()
    examples=[]
    frames=[]
    seen={}
    visits=0
    for t in range(fuel+1):
        # Exact translation-equivariant loop certificate for small configurations.
        if len(tape) < 30:
            key = q,tuple(sorted(p-h for p in tape))
            if key in seen:
                prior_t,prior_h=seen[key]
                return {'start':start,'outcome':'exact_translation_cycle','steps':t,'first_seen':prior_t,'period':t-prior_t,'head_translation':h-prior_h,'ones':len(tape),'dispatch_visits':visits,'dispatch_examples':examples,'valid_shape_frames':frames}
            if len(seen)<100000:
                seen[key]=t,h
        if q==96:
            visits+=1
            f=frame(tape,h)
            if f is not None and len(frames)<20:
                frames.append({'steps':t,'head':h,**f})
            if len(examples)<8:
                examples.append({'steps':t,'head':h,'ones':sorted(p-h for p in tape)[:45]})
        if (q, int(h in tape)) not in rows:
            return {'start':start,'outcome':'halt','steps':t,'dispatch_visits':visits,'dispatch_examples':examples,'valid_shape_frames':frames}
        if t==fuel:
            break
        w,d,q=rows[q,int(h in tape)]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=1 if d=='R' else -1
    return {'start':start,'outcome':'fuel_limit','steps':fuel,'ones':len(tape),'state':q,'head':h,'dispatch_visits':visits,'dispatch_examples':examples,'valid_shape_frames':frames}


def main():
    here=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sources',type=Path,default=here/'sources')
    ap.add_argument('--baseline',type=Path)
    ap.add_argument('--fuel',type=int,default=2000000)
    ap.add_argument('--output',type=Path,default=here/'bootstrap_search.json')
    a=ap.parse_args()
    a.baseline=a.baseline or a.sources/'zfc_254.tm'
    rows=patched(a.baseline)
    starts=sorted({q for q,b in rows})
    classes={}
    for start in starts:
        seen=set();q=start
        while q not in seen:
            seen.add(q)
            if (q,0) not in rows:
                classes[start]=('halt_before_write',q)
                break
            w,d,n=rows[q,0]
            if w:
                classes[start]=('first_write',q)
                break
            q=n
        else:
            classes[start]=('zero_write_cycle',q)
    seeds=sorted({q for kind,q in classes.values() if kind=='first_write'})
    out={'working_states':len(starts),'seed_classes':dict(Counter(str(v) for v in classes.values())),
         'first_write_representatives':seeds,'runs':[],
         'scope':'All blank starts reduced exactly to first-write representatives or zero-writing cycles. Representative runs are finite diagnostics except explicitly identified exact translation cycles.'}
    print('first-write representatives',seeds,flush=True)
    for q in seeds:
        result=simulate(rows,q,a.fuel)
        out['runs'].append(result)
        a.output.write_text(json.dumps(out,indent=2)+'\n')
        print('start',q,'outcome',result['outcome'],'steps',result['steps'],'dispatches',result['dispatch_visits'],'frames',len(result['valid_shape_frames']),flush=True)


if __name__=='__main__':
    main()
