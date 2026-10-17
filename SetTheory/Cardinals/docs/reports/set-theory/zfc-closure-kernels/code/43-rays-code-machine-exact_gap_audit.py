#!/usr/bin/env python3
"""Enumerate fixed-gap contracts using ProveIt's attributed source-35 checker.

This extends its bounded reached-case diagnostic to every program leaf.
It is not a Coq/Lean proof.  Rejection does not itself establish a bad TM run.
The disjoint PC/header representation cannot encode sites longer than the gap.
"""
from pathlib import Path
import argparse, collections, importlib.util, json, time
from affine_gap_audit import leaves

HERE=Path(__file__).resolve().parent

def load_source(path, upstream):
    spec=importlib.util.spec_from_file_location('source35_short_gap',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    mod.REPO=upstream.resolve();mod.NODES=mod.program()
    return mod

def audit(mod,gaps):
    ns=mod.executor();sites=leaves();cases=[]
    for leaf,(p,op,arg) in enumerate(sites):
        r=mod.PHYS[arg] if op in ('CI','CD') else arg
        for branch in ('z','p') if op=='CD' else ('-',):
            cases.append((leaf,p,op,arg,r,branch))
    assert len(cases)==8391
    results=[]
    for gap in gaps:
        begin=time.monotonic();passed=0;failures=[];hist=collections.Counter()
        for i,(leaf,p,op,arg,r,branch) in enumerate(cases):
            good,p2,res=mod.case(ns,p,op,r,branch,gap,exact_gap=True)
            if good:passed+=1
            else:
                reason=res if isinstance(res,str) else repr(res)
                hist[reason]+=1
                failures.append(dict(case=i,leaf=leaf,path=p,op=op,arg=arg,
                                     physical=r,branch=branch,dest=p2,reason=reason))
        row=dict(gap=gap,passed=passed,failed=len(failures),failure_counts=dict(hist),
                 cases=failures,elapsed=time.monotonic()-begin)
        results.append(row)
        print(json.dumps({k:v for k,v in row.items() if k!='cases'}),flush=True)
    suffixes={str(d):dict(collections.Counter(p[32:] for p,_,_ in sites if len(p)==d))
              for d in (33,34)}
    return {'scope':'All-site diagnostic with fixed gap using existing source35 and upstream box summaries. No new kernel proof or calibrated 252-state machine.',
            'prior_source35_commit':'ba00775e2bf56b184d071346867db74f2eb0c621',
            'upstream_commit':'297ab8df7e5de329605c3875b4934643b371a5e3',
            'sites':len(sites),'instruction_cases':len(cases),
            'depth_histogram':dict(collections.Counter(len(p) for p,_,_ in sites)),
            'deep_suffixes_from_offset_32':suffixes,'gaps':results}

def main():
    if not __debug__:raise SystemExit('Run without -O; upstream integrity uses assertions.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source35',type=Path,default=HERE.parent/'source35_runtime252_short_gap.py')
    ap.add_argument('--upstream',type=Path,default=HERE/'upstream')
    ap.add_argument('--gaps',default='32,33,34,35,36,37,38,40')
    ap.add_argument('--output',type=Path,default=HERE/'runtime252_exact_gaps.json')
    a=ap.parse_args();mod=load_source(a.source35,a.upstream)
    a.output.write_text(json.dumps(audit(mod,list(map(int,a.gaps.split(',')))),indent=2)+'\n')

if __name__=='__main__':main()
