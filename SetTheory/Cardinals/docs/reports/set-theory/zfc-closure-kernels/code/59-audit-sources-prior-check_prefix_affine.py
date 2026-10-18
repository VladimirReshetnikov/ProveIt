#!/usr/bin/env python3
"""Check every original instruction using the proved prefix-carry contracts."""
from pathlib import Path
from collections import Counter
import json,hashlib,time
import prefix_affine as affine
import prefix_shift_prototype as proto

def main():
    table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in proto.build().items()}
    counts=Counter();cases=0;minimum=10**9;maximum=0;began=time.monotonic()
    for pc,op,r in proto.sites():
        for zero in ((True,False) if op=='CD' else (None,)):
            branch=(r,zero) if op=='CD' else None
            if op=='CI' or op=='CD' and not zero:succ=proto.inc(pc)
            elif op=='CD':succ=proto.inc(proto.strip(pc,'0',1))
            elif op=='CB':succ=proto.inc(proto.strip(pc,'0',r))
            elif op=='CC':succ=proto.strip(pc,'1',r)
            else:succ=''
            effect=('inc',r) if op=='CI' else ('dec',r) if op=='CD' and not zero else None
            extra=int(op=='CD' and not zero)
            right=([('r',0,1,41+extra),('b',1),('box',('plain',effect))] if succ is None else
                   [('b',int(b)) for b in succ]+[('r',0,1,40+extra-len(succ)),('b',1),('box',('plain',effect))])
            rules,literal=affine.run(table,pc,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1000)
            counts.update(rules);cases+=1;minimum=min(minimum,literal);maximum=max(maximum,sum(rules.values()))
    assert cases==8391 and minimum>0
    out=dict(status='PASS',cases=cases,minimum_literal_steps_per_case=minimum,
             max_rules_per_case=maximum,rule_totals=dict(counts),elapsed_seconds=time.monotonic()-began,
             semantics='All gap parameters n>=0, all nine primary register values satisfying the named decrement guard, every finite nonempty spare suffix.',
             gap_effect='positive decrement +1; overflow +1; all other cases +0',
             spare_effect='increment appends [1]; other operations preserve the suffix',
             scope='Mathematical symbolic check conditional on the four explicitly stated register contracts; not a Lean/Coq check.')
    path=Path(__file__).with_name('prefix-affine-result.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
