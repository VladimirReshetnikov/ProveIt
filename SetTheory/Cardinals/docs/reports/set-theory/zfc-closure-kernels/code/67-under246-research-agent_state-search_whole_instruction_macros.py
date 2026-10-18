#!/usr/bin/env python3
"""Screen macro deletions by entire literal instructions, allowing new phases.

No unchanged register-box contract is assumed in this finite discovery search.
"""
import sys,json,random,time,itertools,argparse
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from search_merges import T,Q,SITES,lib

OFFSET=200

def case(pc,kind,r,positive,seed):
    regs=[(i*3+seed)%7 for i in range(9)]
    if kind=='CD':regs[lib.PHYSICAL[r]]=int(positive)*(seed+1)
    one=lib.paint(pc,40,regs,[0,1],0)
    start=96,OFFSET,sum(1<<(x+OFFSET) for x in one)
    want=lib.expected(pc,kind,r,regs,[0,1],0,40)
    if want:want=(96,want[0]+OFFSET,sum(1<<(x+OFFSET) for x in want[1]))
    return start,want,(pc,kind,r,positive,seed)

def run(rows,start,want,limit):
    q,h,t=start;seen=set()
    for i in range(limit):
        if q==254:return want is None
        if (q,h,t) in seen:return False
        seen.add((q,h,t))
        b=(t>>h)&1;row=rows[2*q+b]
        if row is None:return False
        w,d,q=row
        t=(t|(1<<h)) if w else (t&~(1<<h))
        h+=d
        if h<0 or h>2000:return False
        if (q,h,t)==want:return True
    return False

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--limit',type=int,default=10000)
    a=ap.parse_args();began=time.monotonic()
    rng=random.Random(189);SS=SITES.copy();rng.shuffle(SS)
    tests=[]
    for pc,kind,r in SS:
        for positive in ((False,True) if kind=='CD' else (False,)):
            tests.append(case(pc,kind,r,positive,3))
    # Put CI and zero-CD up front: other modes do not reach many tested rows.
    tests.sort(key=lambda c: not(c[2][1]=='CI' or c[2][1]=='CD' and not c[2][3]))
    rows=[T.get((q,b)) for q in range(256) for b in (0,1)]
    results={}
    for removed,key in [(255,(75,0)),(109,(95,0)),(83,(73,0)),(112,(131,1)),(75,(109,0))]:
        assert [k for k,row in T.items() if row[2]==removed and k[0]!=removed]==[key]
        survivors=[];best=[];tested=0
        for action in itertools.product((0,1),(-1,1),[q for q in Q if q!=removed]):
            D=rows.copy();D[2*removed]=D[2*removed+1]=None;D[2*key[0]+key[1]]=action
            passed=0
            for start,want,description in tests:
                if not run(D,start,want,a.limit):break
                passed+=1
            else:
                survivors.append(list(action))
                actual={k:row for k,row in T.items() if k[0]!=removed};actual[key]=action
                text='#! start 95\n'+''.join(f'{q} {b} {w} '+('R' if d==1 else 'L')+f' {r}\n' for (q,b),(w,d,r) in sorted(actual.items()))
                (HERE/f'candidate_whole_{removed}_{len(survivors)}.tm').write_text(text)
                print('FULL_FINITE_PASS',removed,action,flush=True)
            best.append(dict(action=action,passed=passed,failure=description if passed<len(tests) else None))
            tested+=1
        best.sort(key=lambda r:-r['passed'])
        results[removed]=dict(incoming=key,actions=tested,literal_fuel=a.limit,survivors=survivors,
            maximum_cases_passed=best[0]['passed'],best20=best[:20],
            scope='Finite literal whole-instruction tests; no fixed macro contract or unbounded proof is assumed.')
        print('target',removed,'actions',tested,'survivors',survivors,'best',best[0],'seconds',time.monotonic()-began,flush=True)
        (HERE/'whole_instruction_macro_search.json').write_text(json.dumps(results,indent=2))

if __name__=='__main__':main()
