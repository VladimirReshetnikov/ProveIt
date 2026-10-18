#!/usr/bin/env python3
"""Directed and mixed-row folds of a correct rotated 246-state table."""
import sys,json,time,random
from pathlib import Path
from search_repair import HERE,BASE,base,run,compiler
sys.path.insert(0,str(BASE/'code'))
import check_macro_inductions as macro

def macro_check(t):
    macro.TABLE={(int(q),b):(w,d,int(r)) for (q,b),(w,d,r) in t.items()}
    macro.DERIVED.clear();macro.BLOCK_PROOFS.clear();macro.WORD_IDENTITY_PROVED=False
    macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()

def main():
    start=time.monotonic();n,r,t,cc=base()
    t['218',0]=(0,'R','105');t['208',0]=(0,'R','23');t['208',1]=(1,'R','70');t['237',0]=(0,'R','208')
    macro_check(t)
    states=sorted({q for q,b in t},key=int);byq={q:[] for q in states}
    rr=random.Random(274298);rr.shuffle(cc)
    tracked=compiler.Tracking(t)
    for i,c in enumerate(cc):
        tracked.used.clear();run(tracked,c)
        for q in {q for q,b in tracked.used}:byq[q].append(i)
    counts={};survivors=[];affine_only=[]
    for kind in ['uniform','blend']:
        tested=0;affinepass=0;macropass=0
        for q in states:
            if q=='96':continue
            for r in states:
                if q==r:continue
                if kind=='blend' and r=='96':continue
                u={k:(w,d,r if s==q else s) for k,(w,d,s) in t.items() if k[0]!=q}
                if kind=='blend':
                    w,d,s=t[q,0];u[r,0]=(w,d,r if s==q else s)
                indices=byq[q] if kind=='uniform' else sorted(set(byq[q])|set(byq[r]))
                tested+=1
                try:
                    for i in indices:run(u,cc[i])
                except (AssertionError,KeyError):continue
                affinepass+=1;affine_only.append((kind,q,r))
                try:macro_check(u)
                except (AssertionError,KeyError):continue
                macropass+=1;survivors.append((kind,q,r))
                print('PROVISIONAL PASS',kind,q,r,flush=True)
                (HERE/f'rotated245_{kind}_{q}_{r}.tm').write_text('#! start 95\n'+''.join(f'{v} {b} {w} {d} {s}\n' for (v,b),(w,d,s) in sorted(u.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
            if int(q)%25==0:print('progress',kind,q,tested,affinepass,macropass,'seconds',round(time.monotonic()-start,2),flush=True)
        counts[kind]=dict(tested=tested,affine_pass=affinepass,macro_pass=macropass)
    report=dict(counts=counts,survivors=survivors,affine_only=affine_only,seconds=time.monotonic()-start)
    (HERE/'rotated_merge_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='affine_only'},indent=2),flush=True)

if __name__=='__main__':main()
