"""Exact rooted-graph canonicalization with lexicographic prefix pruning.

Only complete spanning traversals can establish the best candidate. A prefix
strictly greater than the best candidate cannot improve it, so its traversal
may stop. This changes runtime, not the canonicalization relation.
"""
def canonical(rows, states, mirror=False, flip=False, loose=False):
    state_set=set(states); count=len(states); best=None
    for start in states:
        indices={start:0}; order=[start]; out=[]; relation=0; rejected=False
        for q in order:
            for b in (0,1):
                w,d,n=rows[q,b^flip]
                w^=flip
                if mirror: d='L' if d=='R' else 'R'
                if n in state_set:
                    if n not in indices: indices[n]=len(indices); order.append(n)
                    item=(w,d,indices[n])
                else: item=(0,'R',-1) if loose else (w,d,-1)
                if best is not None and relation==0:
                    position=len(out)
                    if item>best[position]: rejected=True; break
                    if item<best[position]: relation=-1
                out.append(item)
            if rejected: break
        if not rejected and len(order)==count:
            candidate=tuple(out)
            if best is None or candidate<best: best=candidate
    return best
