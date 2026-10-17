#!/usr/bin/env python3
"""Eliminate a state by independently certified incoming-edge detours.

Every external incoming edge may use its own arbitrary write/move/target.
The proposed detour never executes the removed state or another edited row
before its positive-progress match. This local exclusion makes the per-edge
certificates compose without a global uniform state map. Literal verification
of the final simultaneous table remains mandatory and is implemented below.
"""
import argparse, collections, itertools, json, time
from pathlib import Path
from synthesize_local_rows import parse, abstract_windows, trace, keys, overlaps


def detour(rows,src,pattern,radius,bound,halt,first,removed,changed_keys,targets):
    h=0; q=src; p=pattern
    for i in range(bound):
        if q==halt or abs(h)>radius or q==removed: return None
        bit=h+radius; key=(q,(p>>bit)&1)
        if i>0 and key in changed_keys: return None
        w,d,q=first if i==0 else rows[key]
        p=(p & ~(1<<bit)) | (w<<bit); h+=d
        k=('halt',) if q==halt else (q,h,p)
        if q!=removed and k in targets: return (targets[k],i+1)
    return None


def edge_options(rows,src,read,patterns,radius,bound,halt,removed,changed_keys,actions):
    possible={a:[] for a in actions if a[2]!=removed}; tests=0; witness=None
    for p in patterns:
        target=keys(trace(rows,src,p,radius,bound,halt),halt)
        target={k:v for k,v in target.items() if k[0]!=removed}
        keep={}
        for a,cert in possible.items():
            tests+=1
            meet=detour(rows,src,p,radius,bound,halt,a,removed,changed_keys,target)
            if meet is not None: keep[a]=cert+[[p,*meet]]
        possible=keep
        if not possible: witness=p; break
    return possible,tests,witness


def main():
    if not __debug__: raise SystemExit('Run without -O: functional checks are assertions.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('--radius',type=int,default=6)
    ap.add_argument('--steps',type=int,default=64)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); rows,start,halt,sha=parse(args.table)
    states=sorted({q for q,b in rows}); began=time.monotonic()
    windows=abstract_windows(rows,start,halt,args.radius)
    actions=list(itertools.product((0,1),(-1,1),states+[halt]))
    results=[]; successes=[]; nchecks=0
    for removed in states:
        if removed==start: continue
        incoming={(q,b) for (q,b),(w,d,t) in rows.items() if t==removed and q!=removed}
        chosen={}; edge_cert=[]; options_counts=[]
        for src,read in sorted(incoming):
            pats=[p for p in windows[src] if (p>>args.radius)&1==read]
            possible,n,witness=edge_options(rows,src,read,pats,args.radius,args.steps,halt,removed,incoming,actions)
            nchecks+=n
            options_counts.append({'source':src,'read':read,'options':len(possible),'contexts':len(pats),'first_failed_window':witness})
            if not possible: break
            a=min(possible); chosen[src,read]=a
            edge_cert.append({'source':src,'read':read,'action':list(a),'certificate':possible[a]})
        result={'removed':removed,'external_incoming_edges':len(incoming),'edges_checked':options_counts,'all_edges_have_bypass':len(chosen)==len(incoming)}
        if result['all_edges_have_bypass']:
            new={k:chosen.get(k,a) for k,a in rows.items() if k[0]!=removed}
            assert len(new)==len(rows)-2 and all(a[2]!=removed for a in new.values())
            # Independent literal check of the assembled simultaneous mutation.
            final=[]
            for (src,b),a in sorted(chosen.items()):
                for p in windows[src]:
                    if (p>>args.radius)&1!=b: continue
                    target=keys(trace(rows,src,p,args.radius,args.steps,halt),halt)
                    target={k:v for k,v in target.items() if k[0]!=removed}
                    meet=overlaps(trace(new,src,p,args.radius,args.steps,halt),target,halt)
                    assert meet is not None,(removed,src,b,p)
                    final.append([src,b,p,*meet])
            entry={'removed':removed,'start':start,'edge_certificates':edge_cert,'assembled_certificate':final}
            successes.append(entry); print('CERTIFIED',removed,flush=True)
        results.append(result)
        if removed%40==0: print('bypass state',removed,'seconds',round(time.monotonic()-began,2),flush=True)
    report={'table':str(args.table),'table_sha256':sha,'working_states':len(states),'start':start,'halt':halt,
      'radius':args.radius,'steps_per_side':args.steps,'abstract_configurations':sum(map(len,windows.values())),
      'removed_states_tested':len(results),'action_domain_size':len(actions),'row_context_checks':nchecks,
      'results':results,'certified_eliminations':successes,'elapsed_seconds':round(time.monotonic()-began,3),
      'scope':'Incoming-edge actions synthesized independently with no edited-row use inside a detour. A negative output is not a lower bound and does not exclude coordinated detours that revisit edited rows, larger windows, longer blocks, or other state-removal methods.'}
    args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('results','certified_eliminations')},indent=2),flush=True)
    print('certified_eliminations',len(successes),flush=True)

if __name__=='__main__': main()
