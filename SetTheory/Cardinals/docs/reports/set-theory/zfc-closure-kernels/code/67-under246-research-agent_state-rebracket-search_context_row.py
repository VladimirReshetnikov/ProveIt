#!/usr/bin/env python3
"""Merge two states with one equal row, synthesizing their other row."""
import sys,json,time,random,itertools
from collections import defaultdict
from search_repair import HERE,BASE,base,run,compiler
from search_rotated_merges import macro,macro_check

class Used(dict):
    def __init__(self,t):super().__init__(t);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def main():
    start=time.monotonic();n,r,t,cc=base()
    t['218',0]=(0,'R','105');t['208',0]=(0,'R','23');t['208',1]=(1,'R','70');t['237',0]=(0,'R','208')
    states=sorted({q for q,b in t},key=int);byq={q:[] for q in states}
    rr=random.Random(274299);rr.shuffle(cc)
    tracked=compiler.Tracking(t)
    for i,c in enumerate(cc):
        tracked.used.clear();run(tracked,c)
        for q in {q for q,b in tracked.used}:byq[q].append(i)
    macro.TABLE=Used({(int(q),b):(w,d,int(r)) for (q,b),(w,d,r) in t.items()})
    macro.DERIVED.clear();macro.BLOCK_PROOFS.clear();macro.WORD_IDENTITY_PROVED=False
    macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()
    protected={(str(q),b) for q,b in macro.TABLE.used}
    prot_states={q for q,b in protected}
    pairs=[]
    for b in [0,1]:
        groups=defaultdict(list)
        for (q,c),a in t.items():
            if c==b:groups[a].append(q)
        for g in groups.values():
            for q,r in itertools.combinations(g,2):
                if q in ('95','96') or q in prot_states:q,r=r,q
                if q in ('95','96') or q in prot_states or (r,1-b) in protected:continue
                pairs.append((q,r,b))
    pairs.sort(key=lambda z:(not ({z[0],z[1]}&{'178','208','218','154','237','244'}),int(z[0]),int(z[1]),z[2]))
    results=[];tested=0
    for q,r,b in pairs:
        u={k:(w,d,r if s==q else s) for k,(w,d,s) in t.items() if k[0]!=q}
        # Prioritize a distinct case from each original state's context.
        indices=list(dict.fromkeys([i for pair in itertools.zip_longest(byq[q],byq[r]) for i in pair if i is not None]))
        survivors=[]
        for w,d,s in itertools.product((0,1),('L','R'),states+['254']):
            if s==q:continue
            u[r,1-b]=(w,d,s)
            if any(u.get(k)!=t[k] for k in protected):continue
            tested+=1
            try:
                for i in indices:run(u,cc[i])
            except (AssertionError,KeyError):continue
            macro_check(u)
            print('PROVISIONAL PASS',q,r,b,(w,d,s),flush=True)
            survivors.append((w,d,s))
            (HERE/f'rotated245_context_{q}_{r}_{b}_{w}{d}{s}.tm').write_text('#! start 95\n'+''.join(f'{v} {c} {x} {m} {a}\n' for (v,c),(x,m,a) in sorted(u.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
        results.append(dict(deleted=q,retained=r,fixed_bit=b,survivors=survivors))
        if len(results)%10==0:print('progress',len(results),'/',len(pairs),tested,'seconds',round(time.monotonic()-start,2),flush=True)
    report=dict(scope='Pairs with one identical literal transition; redirect deleted state globally, retain the common row, synthesize the other row from every write/direction/retained-state-or-halt target; protect the 42 macro-proof rows exactly; affine fuel 1500.',pairs=len(pairs),tested=tested,results=results,seconds=time.monotonic()-start)
    (HERE/'rotated_context_row_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2),flush=True)

if __name__=='__main__':main()
