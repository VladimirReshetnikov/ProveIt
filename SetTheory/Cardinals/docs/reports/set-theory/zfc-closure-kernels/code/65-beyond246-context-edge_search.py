#!/usr/bin/env python3
"""Find safe per-entry fold redirects before trying mixed deletion."""
import argparse,itertools,json,time
from pathlib import Path
import fold_search as f


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('q',type=int)
    args=ap.parse_args();q=args.q
    entries=[k for k,row in f.OLD.items() if row[2]==q and k[0]!=q]
    targets=[p for p in f.STATES if p!=q and f.shared_branch(q,p)]
    accepted={};results=[];began=time.monotonic()
    print('state',q,'entries',entries,'targets',targets,flush=True)
    for entry in entries:
        accepted[entry]=[]
        for p in targets:
            T=f.OLD.copy();w,d,_=T[entry];T[entry]=(w,d,p)
            try:
                record=f.verify(T)
                accepted[entry].append(p)
                print('SAFE EDGE',entry,p,flush=True)
                result='PASS'
            except Exception as exc:
                result=type(exc).__name__+':'+str(exc)
            results.append(dict(entry=entry,target=p,result=result))
        print('DONE EDGE',entry,accepted[entry],flush=True)
    summary=dict(state=q,seconds=time.monotonic()-began,entries=results,
        safe_targets={str(k):v for k,v in accepted.items()})
    (f.ROOT/('edge-search-'+str(q)+'.json')).write_text(json.dumps(summary,indent=2)+'\n')
    if all(accepted.values()):
        for choices in itertools.product(*(accepted[e] for e in entries)):
            T={k:r for k,r in f.OLD.items() if k[0]!=q}
            for e,p in zip(entries,choices):
                w,d,_=T[e];T[e]=(w,d,p)
            try:
                result=f.verify(T)
                label=str(q)+'_'+'_'.join(map(str,choices))
                (f.ROOT/('mixed_'+label+'.tm')).write_text(f.encode(T,f.START))
                (f.ROOT/('mixed_'+label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
                print('SUCCESS',q,entries,choices,flush=True)
                break
            except Exception:pass
    print('FINISH',time.monotonic()-began,flush=True)

if __name__=='__main__':main()
