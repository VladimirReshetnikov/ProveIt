#!/usr/bin/env python3
"""Compose the attributed 40-step reassociation and 80-step local shortcut.

The result still has 253 states. The new computation checks the shortcut's
guard on the reassociated machine, not just on the original baseline, and
verifies the entire blank bootstrap frame. No new state record is claimed.
"""
import argparse, hashlib, json
from pathlib import Path
from synthesize_local_rows import parse, abstract_windows, trace


def run(rows,start,halt,steps):
    q=start; head=0; ones=set(); uses=0
    for i in range(steps):
        assert q!=halt
        b=int(head in ones)
        uses+=int((q,b)==(60,0))
        w,d,q=rows[q,b]
        if w: ones.add(head)
        else: ones.discard(head)
        head+=d
    return {'state':q,'head':head,'one_cells':sorted(ones)},uses


def verify_invariant(rows,start,halt,windows,radius):
    assert 0 in windows[start]
    known={q:set(v) for q,v in windows.items()}; mask=(1 << (2*radius+1))-1
    checks=0
    for q,patterns in windows.items():
        if q==halt: continue
        for p in patterns:
            b=(p>>radius)&1; w,d,t=rows[q,b]
            u=p ^ (((p>>radius)&1)<<radius) ^ (w<<radius)
            successors=((u>>1),(u>>1)|(1<<(2*radius))) if d==1 else ((u<<1)&mask,((u<<1)&mask)|1)
            for n in successors: assert n in known[t]; checks+=1
    return checks


def main():
    if not __debug__: raise SystemExit('Run without -O: functional checks are assertions.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('public',type=Path); ap.add_argument('faster',type=Path)
    ap.add_argument('--output-dir',type=Path,required=True); args=ap.parse_args()
    public,start,halt,ph=parse(args.public); rows,st,ha,fh=parse(args.faster)
    assert (start,halt)==(st,ha)==(0,253)
    assert ph=='84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
    assert fh=='d5b7a357dbf4dd9d18c8e1aa04dc0c3c0e1b8f349853b7558d1a096a15684412'
    changes={k for k in rows if rows[k]!=public[k]}
    assert changes=={(37,0),(37,1),(42,0),(42,1)}
    assert rows[60,0]==(0,-1,45) and rows[45,0]==(0,1,43) and rows[43,0]==(0,1,51)
    windows=abstract_windows(rows,start,halt,2)
    checks=verify_invariant(rows,start,halt,windows,2)
    guarded=[p for p in windows[60] if (p>>2)&1==0]
    assert guarded and all((p>>1)&1==0 for p in guarded)
    candidate=dict(rows); candidate[60,0]=(0,1,51)
    macros=0
    for p in range(32):
        if (p>>1)&3: continue
        old=trace(rows,60,p,2,3,halt); new=trace(candidate,60,p,2,1,halt)
        assert len(old)==3 and old[-1]==new[-1]; macros+=1
    assert macros==8
    original_boot,public_uses=run(public,start,halt,312975)
    faster_boot,faster_uses=run(rows,start,halt,312935)
    target_steps=312935-2*faster_uses
    composed_boot,composed_uses=run(candidate,start,halt,target_steps)
    assert faster_uses==composed_uses==40 and original_boot==faster_boot==composed_boot
    assert composed_boot['state']==33 and composed_boot['head']==-17 and len(composed_boot['one_cells'])==178
    out=args.output_dir; out.mkdir(parents=True,exist_ok=True)
    text='#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for (q,b),(w,d,t) in sorted(candidate.items()))
    (out/'composed253.tm').write_text(text)
    invariant={str(q):str(sum(1<<p for p in ps)) for q,ps in windows.items()}
    (out/'composed_guard_invariant.json').write_text(json.dumps({'source_sha256':fh,'radius':2,'masks':invariant},indent=2)+'\n')
    report={'public_source_sha256':ph,'faster_source_sha256':fh,'composed_sha256':hashlib.sha256(text.encode()).hexdigest(),
        'working_states':253,'transition_rows':506,'start':start,'halt':halt,'composed_changed_rows_from_public':[
          {'state':q,'read':b,'old':list(public[q,b]),'new':list(candidate[q,b])} for q,b in sorted(candidate) if candidate[q,b]!=public[q,b]],
        'invariant_pairs':sum(map(len,windows.values())),'invariant_closure_obligations':checks,
        'guarded_radius2_patterns':guarded,'local_macro_cases':macros,'public_boot_steps':312975,
        'faster_boot_steps':312935,'composed_boot_steps':target_steps,'shortcut_uses_during_boot':composed_uses,
        'complete_bootstrap_configuration':composed_boot,'all_integer_tape_cells_match':True,
        'scope':'New composition of two attributed same-size transformations. The radius-two closed invariant proves the 3-to-1 shortcut valid on every reachable faster253 configuration. This is an ordinary finite-certificate table-to-table proof, not a new proof-assistant build or a state-count improvement.'}
    (out/'composition_result.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='complete_bootstrap_configuration'},indent=2))

if __name__=='__main__': main()
