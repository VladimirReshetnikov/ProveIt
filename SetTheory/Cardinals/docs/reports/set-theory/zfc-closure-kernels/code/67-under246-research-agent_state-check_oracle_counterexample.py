#!/usr/bin/env python3
"""Exact counterexample to an inherited macro after the spurious 131->63 fold."""
from pathlib import Path
import sys,json
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'sources/context246/zfc-context246'
sys.path.insert(0,str(BASE/'code'))
from rebuild_machines import build

def run(table,steps):
    q,h,ones=95,0,{3}
    trace=[dict(step=0,state=q,head=h,ones=sorted(ones))]
    for i in range(steps):
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
        trace.append(dict(step=i+1,state=q,head=h,ones=sorted(ones)))
    return trace

def main():
    table=build()
    candidate={k:(w,d,63 if t==131 else t) for k,(w,d,t) in table.items() if k[0]!=131}
    original_trace=run(table,7);candidate_trace=run(candidate,7)
    assert original_trace[-1]==dict(step=7,state=112,head=-1,ones=[1,3])
    assert candidate_trace[-1]==dict(step=7,state=63,head=-1,ones=[0,2,3])
    # 112 has no non-self incoming row after deleting131, hence can never be
    # reached from95, independently of any finite simulation horizon.
    incoming112=[list(k) for k,v in candidate.items() if v[2]==112]
    assert incoming112==[[112,1]]
    out=dict(status='PASS',purpose='Refute inherited zero-decrement box contract after fold131to63',
       input='marked zero followed by one zero-valued spare:0001, zeros elsewhere',
       original_trace=original_trace,candidate_trace=candidate_trace,
       candidate_incoming112=incoming112,
       conclusion='Original reaches112 at head-1 after7steps with tape0101. Candidate never reaches112 from95 because112 has only its own self-incoming edge.',
       scope='The macro contract is refuted; no claim is made about the altered blank machine or its consistency equivalence.')
    (HERE/'oracle_counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
