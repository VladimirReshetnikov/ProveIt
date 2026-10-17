#!/usr/bin/env python3
"""Formula-to-ground-class compiler and an independent finite clause audit.

The finite audit checks the exact EPSC closure block over every binary E,R
relation on domains of size 2 and 3.  Such finite inputs are not models of
the full assignment/class theory (which forces an infinite domain).
"""
import json
from functools import lru_cache
from pathlib import Path
from represented_epsc_kernel import f, selector_term, term_nodes, term_vars

def atom(i,j): return ('E',i,j)
def nand(a,b): return ('N',a,b)
def exists(i,a): return ('X',i,a)

def class_term(formula, selector='term'):
    """Translate named, equality-free E/NAND/exists syntax to a ground term."""
    tag,*args=formula
    if tag=='E':
        i,j=args
        assert type(i) is int and type(j) is int and min(i,j)>=0
        return f('A',selector_term(i,selector),selector_term(j,selector))
    if tag=='N': return f('N',class_term(args[0],selector),class_term(args[1],selector))
    if tag=='X':
        i,a=args
        assert type(i) is int and i>=0
        return f('Q',selector_term(i,selector),class_term(a,selector))
    if tag=='bottom':
        assert not args
        a=f('A',f('o'),f('o'))
        truth=f('N',a,f('N',a,a))
        return f('N',truth,truth)
    raise ValueError('Unknown formula constructor')

def parameter_assignment(parameters, selector='term'):
    """Dictionary index>=2 -> target-language term; 0/1 are input slots."""
    result=f('o')
    for index,value in sorted(parameters.items()):
        assert type(index) is int and index>=2
        result=f('C',result,selector_term(index,selector),value)
    return result

@lru_cache(None)
def members(mask,n):
    return tuple(i for i in range(n) if mask>>i&1)

def relations(code,n):
    """Rows indexed by first argument, each a mask of second arguments."""
    return tuple((code>>(n*x))&((1<<n)-1) for x in range(n))

def incoming(rows,n):
    return tuple(sum(((rows[x]>>y)&1)<<x for x in range(n)) for y in range(n))

def epsc_direct(e, r, n):
    """Evaluate the original quantified EPSC formula literally, via masks."""
    inn=incoming(e,n)
    bounded=True
    for x in range(n):
        outputs=members(r[x],n)
        if not any(all((inn[y]&~inn[d])==0 for y in outputs) for d in range(n)):
            bounded=False
            break
    if not bounded: return True
    for h in range(n):
        hs=inn[h]
        closure=all((r[x]&~hs)==0 for x in range(n) if inn[x]==0 or (hs>>x&1))
        support=all(any(r[x]>>y&1 for x in range(n)) for y in members(hs,n))
        if closure and support: return True
    return False

def shared_clause_witness(e,r,n):
    """Solve the six universal clauses independently by local Skolem choices.

    Inputs b,t are fixed, so G,K are one chosen flag/value and U,T each have
    n entries.  The two branch values are genuine distinct domain values
    o=0 and q=1; only their equality test is used in this local audit.
    """
    def E(x,y): return bool(e[x]>>y&1)
    def R(x,y): return bool(r[x]>>y&1)
    for kval in range(n):
        witnesses=[]
        for d in range(n):
            possible=next(((u,z) for u in range(n) for z in range(n)
                           if R(kval,u) and E(z,u) and not E(z,d)),None)
            if possible is None: break
            witnesses.append(possible)
        else:
            return {'G':0,'K':kval,'U':[a for a,b in witnesses],
                    'T':[b for a,b in witnesses]}
    for kval in range(n):
        if not all((not E(x,kval)) or (not R(x,y)) or E(y,kval)
                   for x in range(n) for y in range(n)):
            continue
        us=[]
        ts=[]
        for y in range(n):
            witness=next((u for u in range(n) if not E(y,kval) or R(u,y)),None)
            if witness is None: break
            us.append(witness)
        else:
            for x in range(n):
                witness=next((z for z in range(n)
                              if all(E(z,x) or not R(x,y) or E(y,kval)
                                     for y in range(n))),None)
                if witness is None: break
                ts.append(witness)
            else:
                return {'G':1,'K':kval,'U':us,'T':ts}
    return None

def evaluate_six_clauses(e,r,n,witness):
    def E(x,y): return bool(e[x]>>y&1)
    def R(x,y): return bool(r[x]>>y&1)
    B=witness['G']==0
    k=witness['K']; u=witness['U']; z=witness['T']
    for d in range(n):
        if not ((not B) or R(k,u[d])): return False
        if not ((not B) or E(z[d],u[d])): return False
        if not ((not B) or (not E(z[d],d))): return False
    for x in range(n):
        for y in range(n):
            if not (B or E(z[x],x) or not R(x,y) or E(y,k)): return False
            if not (B or not E(x,k) or not R(x,y) or E(y,k)): return False
    for y in range(n):
        if not (B or not E(y,k) or R(u[y],y)): return False
    return True

def audit():
    summary={'scope':'local EPSC formula versus shared Skolem block, not full finite FEC models',
             'domains':[]}
    for n in (2,3):
        total=0; valid=0; bad_branch=0; hull_branch=0
        for ec in range(1<<(n*n)):
            e=relations(ec,n)
            for rc in range(1<<(n*n)):
                r=relations(rc,n)
                direct=epsc_direct(e,r,n)
                witness=shared_clause_witness(e,r,n)
                assert direct==(witness is not None),(n,ec,rc,direct,witness)
                if witness is not None:
                    assert evaluate_six_clauses(e,r,n,witness),(n,ec,rc,witness)
                    valid+=1
                    bad_branch+=witness['G']==0
                    hull_branch+=witness['G']==1
                total+=1
        summary['domains'].append({'size':n,'relation_pairs':total,
                                   'EPSC_true':valid,'unbounded_witnesses':bad_branch,
                                   'hull_witnesses':hull_branch})
    example=exists(2,nand(atom(0,2),nand(atom(2,1),atom(3,2))))
    code=class_term(example)
    assert not term_vars(code)
    summary['example_formula']=example
    summary['example_class_term_nodes']=term_nodes(code)
    summary['selector_tree_nodes']=[term_nodes(selector_term(i)) for i in range(10)]
    Path(__file__).with_name('fak5_local_audit.json').write_text(json.dumps(summary,indent=2)+'\n')
    Path(__file__).with_name('fak5_formula_example.json').write_text(json.dumps({'formula':example,'class_term':code},indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__': audit()
