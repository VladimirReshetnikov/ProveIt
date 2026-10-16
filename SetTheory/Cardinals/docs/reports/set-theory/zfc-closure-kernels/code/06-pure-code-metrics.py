"""Recompute old and new templates in the seeded report's declared tree metric.

Basis: membership, equality, bottom, implication, forall; a matrix occurrence
counts as one hole. Variable payloads, parameter closure and all engine/backend
costs are excluded. All totals are formula nodes, NOT Turing-machine states.
"""
from __future__ import annotations
from collections import Counter
import json
from pathlib import Path

def e(x,y): return ('E',x,y)
def eq(x,y): return ('=',x,y)
def h(x,y): return ('H',x,y)
def imp(a,b): return ('I',a,b)
def all_(x,a): return ('A',x,a)
def neg(a): return imp(a,('F',))
def conj(a,b): return neg(imp(a,neg(b)))
def disj(a,b): return imp(neg(a),b)
def iff(a,b): return conj(imp(a,b),imp(b,a))
def ex(x,a): return neg(all_(x,neg(a)))
def sub(x,y): return all_('z',imp(e('z',x),e('z',y)))
def profile(x,y): return all_('z',iff(e('z',x),e('z',y)))
def ext(): return all_('x',all_('y',imp(profile('x','y'),eq('x','y'))))
def ec():
    return all_('x',all_('y',imp(profile('x','y'),all_('w',iff(e('x','w'),e('y','w'))))))
def ir(): return all_('x',neg(e('x','x')))

def closure(seed='subset',mixed=False):
    bound=sub('y','b')
    if mixed: bound=disj(e('y','b'),bound)
    premise=all_('x',ex('b',all_('y',imp(h('x','y'),bound))))
    initial=eq('x','a') if seed=='point' else sub('x','a')
    cl=all_('x',all_('y',imp(conj(disj(initial,e('x','C')),h('x','y')),e('y','C'))))
    purity=all_('y',imp(e('y','C'),ex('x',h('x','y'))))
    return imp(premise,all_('a',ex('C',conj(cl,purity))))

def counts(t):
    out=Counter({t[0]:1})
    if t[0]=='I': out.update(counts(t[1]));out.update(counts(t[2]))
    if t[0]=='A': out.update(counts(t[2]))
    return out

def main():
    specs={
        'old_T_point':[ext(),closure('point',True)],
        'new_T_point':[ext(),closure('point',False)],
        'old_T_subset':[ext(),closure('subset',True)],
        'new_T_subset':[ext(),closure('subset',False)],
        'old_Q_subset':[ec(),closure('subset',True)],
        'new_Q_subset':[ec(),closure('subset',False)],
        'new_Q_subset_IR':[ec(),closure('subset',False),ir()],
    }
    data={'metric':__doc__.strip(),'theories':{}}
    for name,ts in specs.items():
        c=Counter()
        for t in ts:c.update(counts(t))
        data['theories'][name]={'nodes':sum(c.values()),'constructors':dict(sorted(c.items()))}
    # These are cross-checks against the inspected pinned source, not new input data.
    assert data['theories']['old_T_point']['nodes']==69
    assert data['theories']['old_T_subset']['nodes']==72
    assert data['theories']['old_Q_subset']['nodes']==83
    assert data['theories']['new_T_point']['nodes']==65
    assert data['theories']['new_T_subset']['nodes']==68
    assert data['theories']['new_Q_subset']['nodes']==79
    root=Path(__file__).resolve().parents[1]
    (root/'results'/'metrics.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
if __name__=='__main__':main()
