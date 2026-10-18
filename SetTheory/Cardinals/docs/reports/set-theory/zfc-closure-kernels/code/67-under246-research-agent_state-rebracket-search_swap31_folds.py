#!/usr/bin/env python3
"""Uniform and mixed folds after the disjoint-support source31 commutation."""
import json,time,random,itertools,argparse
from collections import defaultdict
from search_repair import HERE,BASE,cases,run,compiler
from search_rotated_merges import macro,macro_check
from search_context_row import Used

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--combined',action='store_true');args=ap.parse_args()
    began=time.monotonic();rootdir=HERE.parents[1]
    if args.combined:sourcefile=HERE/'combined246_dag.json';tablefile=HERE/'combined246.tm';stem='combined'
    else:sourcefile=rootdir/'agent_audit/layout_search/swap_sparse_31.json';tablefile=rootdir/'root_search/swap31_first.tm';stem='swap31'
    data=json.loads(sourcefile.read_text())
    n={int(k):tuple(map(tuple,v)) for k,v in data['nodes'].items()};r=data['root'];t={}
    for line in tablefile.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,s=line.split();t[q,int(b)]=(int(w),d,s)
    cc=list(cases(n,r));random.Random(314592).shuffle(cc)
    states=sorted({q for q,b in t},key=int);byq=defaultdict(list);bypair=defaultdict(list)
    rec=compiler.Tracking(t)
    for i,c in enumerate(cc):
        rec.used.clear();run(rec,c)
        for q in {q for q,b in rec.used}:byq[q].append(i)
        for key in rec.used:bypair[key].append(i)
    macro.TABLE=Used({(int(q),b):(w,d,int(s)) for (q,b),(w,d,s) in t.items()})
    macro.DERIVED.clear();macro.BLOCK_PROOFS.clear();macro.WORD_IDENTITY_PROVED=False
    macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()
    protected={(str(q),b) for q,b in macro.TABLE.used};protstates={q for q,b in protected}
    results={};survivors=[]
    for kind in ['uniform','blend']:
        tested=0;failures=0
        for q in states:
            if q=='96' or q in protstates:continue
            for s in states:
                if q==s:continue
                if kind=='blend' and (s=='96' or (s,0) in protected):continue
                u={k:(w,d,s if a==q else a) for k,(w,d,a) in t.items() if k[0]!=q}
                if kind=='blend':
                    w,d,a=t[q,0];u[s,0]=(w,d,s if a==q else a)
                if any(u.get(k)!=t[k] for k in protected):continue
                tested+=1
                if kind=='uniform':indices=byq[q]
                else:
                    priorities=bypair[q,1][:4]+bypair[s,0][:4]
                    indices=list(dict.fromkeys(priorities+byq[q]+byq[s]))
                try:
                    for i in indices:run(u,cc[i])
                except (AssertionError,KeyError):failures+=1;continue
                macro_check(u);survivors.append((kind,q,s));print('PROVISIONAL PASS',kind,q,s,flush=True)
                (HERE/f'{stem}_245_{kind}_{q}_{s}.tm').write_text('#! start 95\n'+''.join(f'{v} {b} {w} {d} {a}\n' for (v,b),(w,d,a) in sorted(u.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
            if int(q)%25==0:print('progress',kind,q,tested,'seconds',round(time.monotonic()-began,3),flush=True)
        results[kind]=dict(tested=tested,rejected=failures)
    report=dict(scope='All directed uniform and mixed-row folds of selected table preserving the42 macro-support rows literally; retain dispatcher96; affected universal source guards, affine fuel1500.',combined=args.combined,results=results,survivors=survivors,seconds=time.monotonic()-began)
    (HERE/(stem+'_fold_results.json')).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
