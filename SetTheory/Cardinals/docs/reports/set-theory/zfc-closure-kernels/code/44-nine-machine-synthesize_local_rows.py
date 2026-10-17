#!/usr/bin/env python3
"""Conservative, independently checkable two-row state-fusion synthesis.

This searches a different family from retaining either old state's two rows.
It first finds action detours against the unmodified machine, on every
reachable finite window, then intersects the available actions for pairs of
states. Each resulting *simultaneous* fusion is checked literally against the
modified table, with strictly positive progress on both sides. First-stage
detours are only a proposal heuristic; only the final certificate is sound.

A negative output is a bounded synthesis result, never a state lower bound.
"""
from __future__ import annotations
import argparse, collections, hashlib, itertools, json, time
from pathlib import Path


def parse(path):
    raw = Path(path).read_bytes()
    rows = {}; start = None
    for line in raw.decode().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line.strip() and not line.startswith('#'):
            q, b, w, d, t = line.split()
            key = (int(q), int(b))
            assert key not in rows and d in ('L', 'R')
            rows[key] = (int(w), 1 if d == 'R' else -1, int(t))
    states = sorted({q for q,b in rows})
    assert set(rows) == {(q,b) for q in states for b in (0,1)}
    assert all(w in (0,1) for w,d,t in rows.values()) and start in states
    halt, = {t for w,d,t in rows.values()} - set(states)
    return rows, start, halt, hashlib.sha256(raw).hexdigest()


def abstract_windows(rows, start, halt, radius):
    width = 2*radius+1; mask = (1 << width)-1
    todo = collections.deque([(start,0)]); seen = {(start,0)}
    groups = collections.defaultdict(list)
    while todo:
        q,p = todo.popleft(); groups[q].append(p)
        if q == halt: continue
        w,d,t = rows[q,(p >> radius)&1]
        p = (p & ~(1 << radius)) | (w << radius)
        if d == 1: base,extra = p >> 1, 1 << (width-1)
        else: base,extra = (p << 1)&mask, 1
        for v in (base,base|extra):
            a=(t,v)
            if a not in seen: seen.add(a); todo.append(a)
    return {q:sorted(v) for q,v in groups.items()}


def trace(rows,q,p,radius,bound,halt,first=None):
    h=0; out=[]
    for i in range(bound):
        if q == halt or abs(h)>radius: break
        bit=h+radius
        w,d,q = first if i==0 and first is not None else rows[q,(p >> bit)&1]
        p=(p & ~(1 << bit)) | (w << bit); h+=d
        out.append((q,h,p))
    return out


def keys(trace,halt,mapping=None):
    out={}
    for i,(q,h,p) in enumerate(trace,1):
        k=('halt',) if q==halt else ((mapping.get(q,q) if mapping else q),h,p)
        out.setdefault(k,i)
    return out


def overlaps(trace,targets,halt):
    for i,(q,h,p) in enumerate(trace,1):
        k=('halt',) if q==halt else (q,h,p)
        if k in targets: return (targets[k],i)
    return None


def action_detours(rows,q,b,patterns,radius,bound,halt,actions):
    # All contexts are checked; their deterministic order is retained.
    possible=set(actions); tests=0
    for p in patterns:
        target=keys(trace(rows,q,p,radius,bound,halt),halt)
        keep=set()
        for a in possible:
            tests+=1
            if a==rows[q,b] or overlaps(trace(rows,q,p,radius,bound,halt,a),target,halt):
                keep.add(a)
        possible=keep
        assert rows[q,b] in possible
        if len(possible)==1: break
    return possible,tests


def fused(rows,start,removed,retained,a0,a1):
    result={}
    for (q,b),a in rows.items():
        if q==removed: continue
        if q==retained: a=(a0,a1)[b]
        w,d,t=a
        result[q,b]=(w,d,retained if t==removed else t)
    return result,retained if start==removed else start


def certificate(rows,new,removed,retained,windows,radius,bound,halt):
    cert=[]
    for q in (removed,retained):
        for p in windows[q]:
            target=keys(trace(rows,q,p,radius,bound,halt),halt,{removed:retained})
            meet=overlaps(trace(new,retained,p,radius,bound,halt),target,halt)
            if meet is None: return None,(q,p)
            cert.append([q,p,*meet])
    return cert,None


def main():
    if not __debug__: raise SystemExit('Run without -O: functional checks are assertions.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('--radius',type=int,default=5)
    ap.add_argument('--steps',type=int,default=32)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); assert args.radius>=1 and args.steps>=1
    rows,start,halt,sha=parse(args.table); states=sorted({q for q,b in rows})
    began=time.monotonic(); windows=abstract_windows(rows,start,halt,args.radius)
    actions=list(itertools.product((0,1),(-1,1),states+[halt]))
    alternatives={}; ledger=[]; tests=0
    for q in states:
        for b in (0,1):
            pats=[p for p in windows.get(q,[]) if (p>>args.radius)&1==b]
            alts,n=action_detours(rows,q,b,pats,args.radius,args.steps,halt,actions)
            alternatives[q,b]=alts; tests+=n
            ledger.append({'state':q,'read':b,'contexts':len(pats),'actions':[list(a) for a in sorted(alts)]})
        if q%40==0: print('action synthesis state',q,'seconds',round(time.monotonic()-began,2),flush=True)
    successes=[]; first_failures=[]; tested=0; retained_only=0
    for p,q in itertools.combinations(states,2):
        a0=alternatives[p,0]&alternatives[q,0]
        a1=alternatives[p,1]&alternatives[q,1]
        for z,o in itertools.product(sorted(a0),sorted(a1)):
            # Try both choices of representative because redirects inside the
            # proposed action can change its literal post-fusion behavior.
            for removed,retained in ((p,q),(q,p)):
                new,initial=fused(rows,start,removed,retained,z,o)
                cert,failed=certificate(rows,new,removed,retained,windows,args.radius,args.steps,halt)
                recipe={'removed':removed,'retained':retained,'zero':list(z),'one':list(o)}
                tested+=1
                if z in (rows[p,0],rows[q,0]) and o in (rows[p,1],rows[q,1]): retained_only+=1
                if cert is not None:
                    entry={**recipe,'start':initial,'windows':cert}
                    successes.append(entry)
                    print('CERTIFICATE',recipe,flush=True)
                else: first_failures.append({**recipe,'first_failure':list(failed)})
    report={'table':str(args.table),'table_sha256':sha,'working_states':len(states),'start':start,'halt':halt,
       'radius':args.radius,'steps_per_side':args.steps,'abstract_configurations':sum(map(len,windows.values())),
       'action_domain_size':len(actions),'row_context_checks':tests,'rows_with_nontrivial_action_alternatives':sum(len(a)>1 for a in alternatives.values()),
       'action_alternatives':ledger,'simultaneous_fusion_recipes_checked':tested,
       'recipes_using_only_rows_of_the_merged_states':retained_only,'first_failures':first_failures,'certified_fusions':successes,
       'elapsed_seconds':round(time.monotonic()-began,3),
       'scope':'Finite-window two-row action synthesis. A success has a positive-progress whole-tape block certificate; a negative result is not a lower bound. The action-detour heuristic is not exhaustive over all arbitrary two-row fusions.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('action_alternatives','first_failures','certified_fusions')},indent=2),flush=True)
    print('certified_fusions',len(successes),flush=True)

if __name__=='__main__': main()
