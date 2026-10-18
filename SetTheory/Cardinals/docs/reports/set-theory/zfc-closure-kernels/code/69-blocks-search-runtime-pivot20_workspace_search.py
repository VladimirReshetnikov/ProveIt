#!/usr/bin/env python3
"""Context246 merge20→143 with full action repairs, workspace symbolic oracle.

Only the pointwise transported original macro contracts are assumed. Unknown
rows stop a partial trace without success; complete survivors must pass every
source guard accepted by the independently checked exact-root invariant.
"""
from pathlib import Path
import sys, json, time, itertools
from collections import Counter
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'search/context'))
from search_common import cases, T
sys.path.insert(0,str(ROOT/'code'))
import workspace_block_affine as A
CASES=[c for c in cases if A.case_allowed(c[0],c[1])]
class Pending(Exception):pass
class Partial(dict):
    blocked=frozenset()
    def __getitem__(self,key):
        if key in self.blocked:raise Pending(key)
        return super().__getitem__(key)

def run(table, case):
    pc,branch,target,halt=case
    try:A.run(table,pc,branch,target,halt=halt,fuel=3000)
    except Pending:return 2
    except Exception as err:return 0
    return 1


def main():
    P=Partial({e:(w,d,'143' if t=='20' else t) for e,(w,d,t) in T.items() if e[0]!='20'})
    P['143',0]=(1,'L','2');P['143',1]=(0,'L','2')
    ka=('120',0);kb=('252',1)
    states=sorted({q for q,b in P},key=int)
    actions=[(w,d,q) for q in states for w in (0,1) for d in ('L','R')]
    zeros=[(1,'L','2'),(1,'R','30'),(1,'R','57')]
    ones=[(0,'L','2'),(0,'R','2'),(0,'L','4'),(0,'R','4'),(0,'L','6'),(0,'L','9')]
    output={'source_guards':len(CASES),'actions_per_row':len(actions),'variants':[],'survivors':[]}
    start=time.monotonic()
    for z,o in itertools.product(zeros,ones):
        P['143',0]=z;P['143',1]=o;P.blocked=frozenset((ka,kb))
        relevant=[];basefail=None
        for i,case in enumerate(CASES):
            r=run(P,case)
            if r==0:basefail=i;break
            if r==2:relevant.append(i)
        if basefail is not None:
            output['variants'].append({'zero':z,'one':o,'base_failure':CASES[basefail][:2]})
            print('BASE FAILURE',z,o,CASES[basefail][:2],flush=True)
            continue
        record={'zero':z,'one':o,'pending':len(relevant),'partial':[],'complete_trials':0}
        hits=Counter();P.blocked=frozenset((kb,))
        for a in actions:
            P[ka]=a
            pending=[];bad=False
            for i in sorted(relevant,key=lambda i:-hits[i]):
                r=run(P,CASES[i])
                if r==0:hits[i]+=1;bad=True;break
                if r==2:pending.append(i)
            if bad:continue
            record['partial'].append({'action':a,'pending':len(pending)})
            print('PARTIAL',z,o,a,'pending',len(pending),flush=True)
            P.blocked=frozenset()
            bhits=Counter()
            for b in actions:
                P[kb]=b;good=True;record['complete_trials']+=1
                for i in sorted(pending,key=lambda i:-bhits[i]):
                    if run(P,CASES[i])!=1:bhits[i]+=1;good=False;break
                if good:
                    # Earlier passed cases avoided kb but can use a; unchanged by b.
                    candidate={'zero':z,'one':o,'120/0':a,'252/1':b}
                    assert all(run(P,c)==1 for c in CASES)
                    output['survivors'].append(candidate)
                    name=Path(__file__).with_name('pivot20-workspace-survivor-%d.tm'%len(output['survivors']))
                    name.write_text('\n'.join('%s %d %d %s %s'%(q,s,*P[q,s]) for q in states for s in (0,1))+'\n')
                    print('SURVIVOR',candidate,str(name),flush=True)
            P.blocked=frozenset((kb,))
        output['variants'].append(record);output['seconds']=time.monotonic()-start
        Path(__file__).with_name('pivot20-workspace-results.json').write_text(json.dumps(output,indent=2)+'\n')
        print('VARIANT COMPLETE',z,o,'partials',len(record['partial']),'trials',record['complete_trials'],'seconds',output['seconds'],flush=True)
    print('DONE',len(output['survivors']),'survivors',flush=True)


if __name__=="__main__":
    main()
