"""Independent decorated-word replay, not the producer's core constructor.

Each node stores the reduced image as a^prefix * middle * a^suffix, where
middle starts and ends in a non-multiplier letter. Only the root seam is
cyclically normalized. This recurrence uses no producer gap summaries.
"""
from .slp import Grammar


def reference_image(g,roots,a,z):
    g.validate_roots(roots); out=Grammar(); tab={0:(0,0,0)}
    for n in g.reachable(roots):
        rule=g.rules[n]
        if rule[0]=='t':
            x=rule[1]
            tab[n]=((1 if x==a else -1),0,0) if abs(x)==abs(a) else (
                -z.get(-x,0),out.letter(x),z.get(x,0))
        elif rule[0]=='c':
            p,m,s=tab[rule[1]]; q,h,t=tab[rule[2]]
            if not m and not h: tab[n]=(p+q,0,0)
            elif not m: tab[n]=(p+q,h,t)
            elif not h: tab[n]=(p,m,s+q)
            else:
                mid=out.concat(m,out.concat(out.run(a,s+q),h))
                tab[n]=(p,mid,t)
        else:
            p,m,s=tab[rule[1]]; k=rule[2]
            if not m: tab[n]=(k*p,0,0)
            else:
                tail=out.power(out.concat(out.run(a,s+p),m),k-1)
                tab[n]=(p,out.concat(m,tail),s)
    result=[]
    for root in roots:
        p,m,s=tab[root]
        result.append(out.run(a,p) if not m else out.concat(m,out.run(a,s+p)))
    out.validate_roots(result)
    return out,result
