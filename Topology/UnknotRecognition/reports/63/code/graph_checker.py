"""Independent local cycle/product and connectivity checker.

No imports from the graph producer. Acceptance verifies an inference conditional
on knot-group provenance and valid supplied edge relations, not that provenance.
"""
from __future__ import annotations


def _product_tree(items):
    items=list(items)
    if not items: return 1
    while len(items)>1:
        items=[items[i]*items[i+1] if i+1<len(items) else items[i]
               for i in range(0,len(items),2)]
    return items[0]


def verify(vertices, edges, certificate) -> bool:
    try:
        vs=set(vertices)
        if len(vs)!=len(vertices) or any(type(v) is not int or v<=0 for v in vertices): return False
        if set(certificate)!={'killed','witnesses'}: return False
        killed=certificate['killed']; witnesses=certificate['witnesses']
        if not isinstance(killed,list) or not isinstance(witnesses,list): return False
        if any(type(v) is not int for v in killed) or killed!=sorted(set(killed)): return False
        roots={v:v for v in vs}; sizes={v:1 for v in vs}
        def root(v):
            while roots[v]!=v:
                roots[v]=roots[roots[v]]; v=roots[v]
            return v
        for e in edges:
            if any(type(z) is not int for z in (e.s,e.t,e.a,e.b)): return False
            if e.s not in vs or e.t not in vs or not e.a or not e.b or type(e.plain) is not bool: return False
            p,q=root(e.s),root(e.t)
            if p!=q:
                if sizes[p]<sizes[q]: p,q=q,p
                roots[q]=p; sizes[p]+=sizes[q]
        dead=set()
        for w in witnesses:
            if not isinstance(w,dict) or set(w)!={'mode','walk'}: return False
            if w['mode'] not in ('plain','modulus'): return False
            walk=w['walk']
            if not isinstance(walk,list) or not walk or len(walk)>len(vs)+1: return False
            numer=[]; denom=[]; start=None; current=None; seen=set()
            for step in walk:
                if not isinstance(step,list) or len(step)!=2: return False
                j,d=step
                if type(j) is not int or type(d) is not int or d not in (-1,1) or not 0<=j<len(edges): return False
                e=edges[j]
                if w['mode']=='plain' and not e.plain: return False
                s,t,a,b=(e.s,e.t,e.a,e.b) if d==1 else (e.t,e.s,e.b,e.a)
                if start is None: start=current=s
                if s!=current or s in seen: return False
                seen.add(s); current=t; numer.append(a); denom.append(b)
            if current!=start: return False
            A,B=_product_tree(numer),_product_tree(denom)
            if w['mode']=='plain':
                if A==B: return False
            elif abs(A)==abs(B): return False
            dead.add(root(start))
        expected=sorted(v for v in vs if root(v) in dead)
        return killed==expected
    except (KeyError,TypeError,ValueError,IndexError,AttributeError):
        return False
