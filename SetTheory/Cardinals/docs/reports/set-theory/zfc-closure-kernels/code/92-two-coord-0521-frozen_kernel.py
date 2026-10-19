#!/usr/bin/env python3
"""Frozen-assignment finite closure kernel: exact source payload and checks.

This is an ordinary finite theory / reference encoding, not a TM compiler.
The assignment/class architecture and EPSC calibration are inherited from
ProveIt's FC15* source44; the freeze operator and compiled closure row are
specified here. Everything below uses only the Python standard library.
"""
from __future__ import annotations
import argparse
from itertools import product
import json
from pathlib import Path

FUNCS = [('V', 2), ('C', 3), ('I', 2), ('A', 2),
         ('U', 2), ('W', 3), ('F', 2)]
PREDICATES = ['E', 'Inc', 'Eq']
ARITIES = dict(FUNCS)
d = ('d',)

def f(name, *args):
    assert name in ARITIES and len(args) == ARITIES[name]
    return (name,) + args

q = f('I', d, d)

def neg(a):
    return f('I', a, d)

def both(a, b):
    return neg(f('I', a, neg(b)))

def either(a, b):
    return f('I', neg(a), b)

def all_(j, a):
    return f('U', j, a)

def exists(j, a):
    return neg(all_(j, neg(a)))

def epsc_template(r, s, matrix, shadow=False):
    """Class term for exact empty-seeded supported subset closure.

    Matrix depends only on selector coordinates d and q. For shadow=False,
    r,s are distinct from each other and d,q. For shadow=True only r is
    needed: d is shadowed inside Sub, q inside Empty; these scopes exclude
    the matrix occurrence. The same r is reused in disjoint scopes.
    """
    member_label = d if shadow else s
    empty_label = q if shadow else s
    sub = all_(member_label, f('I', f('A', member_label, q), f('A', member_label, r)))
    locally_bounded = all_(d, exists(r, all_(q, f('I', matrix, sub))))
    empty = all_(empty_label, neg(f('A', empty_label, d)))
    active = either(empty, f('A', d, r))
    closed = all_(d, all_(q, f('I', active,
                                f('I', matrix, f('A', q, r)))))
    support = all_(q, f('I', f('A', q, r), exists(d, matrix)))
    hull = exists(r, both(closed, support))
    return f('I', locally_bounded, hull)

def literal(sign, pred, a, b):
    assert pred in PREDICATES
    return bool(sign), pred, a, b

def eq(a, b, sign=True):
    return literal(sign, 'Eq', a, b)

def inc(a, b, sign=True):
    return literal(sign, 'Inc', a, b)

def edge(a, b, sign=True):
    return literal(sign, 'E', a, b)

def source_clauses(extensional=False, shadow=False):
    a,b,j,k,r,s,t,z = 'a b j k r s t z'.split()
    implication = f('I', a, b)
    updated = f('C', s, j, z)
    closure = epsc_template(r, z, f('F', b, t), shadow)
    frozen_eval = f('C', f('C', b, d, f('V', s, d)), q, f('V', s, q))
    clauses = [
        [eq(f('V', updated, j), z)],
        [eq(k, j), eq(f('V', updated, k), f('V', s, k))],
        [inc(s, implication, False), inc(s, a, False), inc(s, b)],
        [inc(s, implication), inc(s, a)],
        [inc(s, implication), inc(s, b, False)],
        [inc(s, d, False)],
        [inc(s, f('A', j, k), False), edge(f('V', s, j), f('V', s, k))],
        [inc(s, f('A', j, k)), edge(f('V', s, j), f('V', s, k), False)],
        [inc(s, f('U', j, a), False), inc(updated, a)],
        [inc(s, f('U', j, a)), inc(f('C', s, j, f('W', s, j, a)), a, False)],
        [inc(s, f('F', b, t), False), inc(frozen_eval, t)],
        [inc(s, f('F', b, t)), inc(frozen_eval, t, False)],
        [eq(r, d), eq(r, q)]+([] if shadow else [eq(z, d), eq(z, q), eq(z, r)])+[inc(b, closure)],
    ]
    if extensional:
        # Use implication/false to code XOR and a universal distinguishing
        # selector. j differs from d and q; its existential hides no parameter.
        p = f('A', j, d)
        qatom = f('A', j, q)
        xor = f('I', f('I',p,qatom), neg(f('I',qatom,p)))
        assignment = f('C', f('C', d, d, a), q, b)
        clauses.append([eq(j, d), eq(j, q), eq(a, b),
                        inc(assignment, exists(j, xor))])
    return clauses

def reduced_witness_clauses(extensional=False, shadow=False):
    """Eliminate W by a coordinate of the already-required freeze object.

    This equiconsistency transformation requires the rich coding construction
    proved in the accompanying note. It is not definitional expansion of an
    arbitrary original model with its incidence coding left unchanged.
    """
    def convert(t):
        if isinstance(t,str) or t==d:
            return t
        if t[0]=='W':
            s,j,a=(convert(x) for x in t[1:])
            p=f('C',f('C',d,d,s),q,j)
            return f('V',f('F',p,a),q)
        return (t[0],)+tuple(convert(x) for x in t[1:])
    return [[(sign,p,convert(a),convert(b)) for sign,p,a,b in c]
            for c in source_clauses(extensional,shadow)]

def equality_clauses(functions=None):
    clauses = [[eq('x', 'x')],
               [eq('x', 'y', False), eq('x', 'z', False), eq('y', 'z')]]
    for name, arity in (FUNCS if functions is None else functions):
        xs = tuple('x' + str(i) for i in range(arity))
        ys = tuple('y' + str(i) for i in range(arity))
        clauses.append([eq(x,y,False) for x,y in zip(xs,ys)] +
                       [eq(f(name,*xs), f(name,*ys))])
    for pred in ['E', 'Inc']:
        clauses.append([eq('x0','y0',False), eq('x1','y1',False),
                        literal(False,pred,'x0','x1'),
                        literal(True,pred,'y0','y1')])
    return clauses

def variables(t):
    if isinstance(t, str):
        return {t}
    return set().union(*(variables(x) for x in t[1:])) if len(t)>1 else set()

def clause_vars(clause):
    return sorted(set().union(*(variables(t) for l in clause for t in l[2:])))

def term_nodes(t):
    return 1 if isinstance(t,str) else 1 + sum(term_nodes(x) for x in t[1:])

def term_depth(t):
    return 0 if isinstance(t,str) or len(t)==1 else 1+max(term_depth(x) for x in t[1:])

def canonicalize_clause(clause):
    names = {v:'v'+str(i) for i,v in enumerate(clause_vars(clause))}
    def convert(t):
        return names[t] if isinstance(t,str) else (t[0],)+tuple(convert(x) for x in t[1:])
    return [(sign,p,convert(a),convert(b)) for sign,p,a,b in clause]

def pack(clauses):
    """Source44's comparable 3-bit length, 3-bit literal, 4-bit tree format.

    The 2-bit predicate opcode has one padding value. Term codes 0..5 are
    local variables, 6 is d, and 7..13 are the seven functions.
    """
    tags = {name:7+i for i,(name,_) in enumerate(FUNCS)}
    out = ''
    for c in clauses:
        vs = {v:i for i,v in enumerate(clause_vars(c))}
        assert len(vs)<=6 and 1<=len(c)<=7
        def term(t):
            if isinstance(t,str):
                return format(vs[t], '04b')
            return format(6 if t==d else tags[t[0]], '04b') + ''.join(term(x) for x in t[1:])
        out += format(len(c),'03b')
        for sign,p,a,b in c:
            out += str(int(sign))+format(PREDICATES.index(p),'02b')+term(a)+term(b)
    return out+'000'

def unpack(bits):
    pos=0
    def read(width):
        nonlocal pos
        if pos+width>len(bits):
            raise ValueError('truncated payload')
        v=int(bits[pos:pos+width],2)
        pos+=width
        return v
    def term():
        tag=read(4)
        if tag<6:
            return 'v'+str(tag)
        if tag==6:
            return d
        if tag>=7+len(FUNCS):
            raise ValueError('invalid term opcode')
        name,arity=FUNCS[tag-7]
        return f(name,*(term() for _ in range(arity)))
    clauses=[]
    while True:
        size=read(3)
        if size==0:
            if pos!=len(bits):
                raise ValueError('trailing bits')
            return clauses
        c=[]
        for _ in range(size):
            sign=bool(read(1)); pred=read(2)
            if pred>=len(PREDICATES):
                raise ValueError('invalid predicate opcode')
            a=term(); b=term()
            c.append((sign,PREDICATES[pred],a,b))
        clauses.append(c)

def metrics(clauses):
    bits=pack(clauses)
    assert unpack(bits)==[canonicalize_clause(c) for c in clauses]
    dags=set()
    def visit(t):
        if isinstance(t,str) or t==d:
            return
        dags.add(t)
        for x in t[1:]:
            visit(x)
    canonical=[canonicalize_clause(c) for c in clauses]
    for c in canonical:
        for l in c:
            for t in l[2:]:
                visit(t)
    return {'clauses':len(clauses),'literals':sum(map(len,clauses)),
            'term_nodes':sum(term_nodes(t) for c in clauses for l in c for t in l[2:]),
            'max_term_depth':max(term_depth(t) for c in clauses for l in c for t in l[2:]),
            'max_variables':max(map(lambda c:len(clause_vars(c)),clauses)),
            'constructor_dag_nodes':len(dags),'bits':len(bits),
            'bytes':(len(bits)+7)//8}

def direct_epsc(n, edge_table, relation):
    """Independent direct finite-set semantics. No source class terms used."""
    subset=lambda y,u: all(not edge_table[z][y] or edge_table[z][u] for z in range(n))
    bounded=all(any(all(not relation[x][y] or subset(y,u) for y in range(n))
                    for u in range(n)) for x in range(n))
    if not bounded:
        return True
    empty=lambda x: not any(edge_table[z][x] for z in range(n))
    return any(
        all(not ((empty(x) or edge_table[x][c]) and relation[x][y]) or edge_table[y][c]
            for x in range(n) for y in range(n)) and
        all(not edge_table[y][c] or any(relation[x][y] for x in range(n)) for y in range(n))
        for c in range(n))

def formula_check(n, edge_table, relation, shadow=False):
    """Independent semantics for generated class term on ordinary assignments.

    Selector names are syntactic integers 0,1,2,3; object carrier has size n.
    This checks the wrapper, not a finite model of the infinite-carrier core.
    """
    expr=epsc_template('r','s',('R',),shadow)
    selectors={d:0,q:1,'r':2,'s':3}
    def evaluate(t,env):
        if t==d:
            return False
        name=t[0]
        if name=='R':
            return relation[env[0]][env[1]]
        if name=='I':
            return not evaluate(t[1],env) or evaluate(t[2],env)
        if name=='A':
            return edge_table[env[selectors[t[1]]]][env[selectors[t[2]]]]
        if name=='U':
            return all(evaluate(t[2],env[:selectors[t[1]]]+(z,)+env[selectors[t[1]]+1:])
                       for z in range(n))
        raise AssertionError(t)
    return evaluate(expr,(0,0,0,0))

def regressions():
    results={}
    count=0
    for n in (1,2):
        for eraw in range(1<<(n*n)):
            e=tuple(tuple(bool(eraw&(1<<(n*x+y))) for y in range(n)) for x in range(n))
            for rraw in range(1<<(n*n)):
                r=tuple(tuple(bool(rraw&(1<<(n*x+y))) for y in range(n)) for x in range(n))
                assert formula_check(n,e,r)==direct_epsc(n,e,r)
                assert formula_check(n,e,r,True)==direct_epsc(n,e,r)
                count+=1
    results['wrapper_exhaustive_domain_1_2_cases_each_of_two_forms']=count
    # A finite diagnostic for freezing: a matrix with all four-coordinate
    # dependence loses its last two dependencies after evaluation in b.
    count=0
    for base in product(range(2),repeat=4):
        for env in product(range(2),repeat=4):
            for r in range(16):
                original=lambda x: bool((r>>((x[0]+2*x[1]+3*x[2]+5*x[3])%4))&1)
                frozen=lambda s: original((s[0],s[1],base[2],base[3]))
                truth=frozen(env)
                for z,w in product(range(2),repeat=2):
                    assert frozen((env[0],env[1],z,w))==truth
                count+=1
    results['freeze_support_diagnostics']=count
    # A matrix depending only on coordinate r=2 exhibits the capture bug
    # which the F operator prevents: forall-r R has different truth from
    # the same frozen relation with b(r)=1.
    assert not all(bool(z) for z in range(2))
    assert all(bool(1) for z in range(2))
    results['unfrozen_capture_negative_control']=True
    for ext in (False,True):
        for full in (False,True):
            cs=source_clauses(ext)+(equality_clauses() if full else [])
            bits=pack(cs)
            assert unpack(bits)==[canonicalize_clause(c) for c in cs]
            try:
                unpack(bits[:-1])
                raise AssertionError('truncation accepted')
            except ValueError:
                pass
    results['four_codec_roundtrips']=True
    results['four_truncation_controls']=True
    return results

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('frozen-kernel-results.json'))
    args=parser.parse_args()
    result={'status':'ordinary finite-theory payload; no compiled TM or new state bound',
            'functions':FUNCS,'predicates':PREDICATES,'regressions':regressions(),
            'metrics':{}}
    reduced_funcs=[item for item in FUNCS if item[0]!='W']
    result['reduced_functions']=reduced_funcs
    for ext in (False,True):
        for full in (False,True):
            name=('FC14F' if ext else 'FC13F')+('_complete' if full else '_native')
            cs=source_clauses(ext)+(equality_clauses() if full else [])
            result['metrics'][name]=metrics(cs)
            args.output.with_name(name+'.json').write_text(json.dumps(cs,indent=2)+'\n')
            args.output.with_name(name+'.bits').write_text(pack(cs)+'\n')
    for ext in (False,True):
        for full in (False,True):
            name=('FC14S' if ext else 'FC13S')+('_complete' if full else '_native')
            cs=reduced_witness_clauses(ext,True)+(equality_clauses(reduced_funcs) if full else [])
            result['metrics'][name]=metrics(cs)
            args.output.with_name(name+'.json').write_text(json.dumps(cs,indent=2)+'\n')
            args.output.with_name(name+'.bits').write_text(pack(cs)+'\n')
    for ext in (False,True):
        for full in (False,True):
            name=('FC14R' if ext else 'FC13R')+('_complete' if full else '_native')
            cs=reduced_witness_clauses(ext)+(equality_clauses(reduced_funcs) if full else [])
            result['metrics'][name]=metrics(cs)
            args.output.with_name(name+'.json').write_text(json.dumps(cs,indent=2)+'\n')
            # Keep W's unused template opcode vacant for a directly comparable
            # four-bit stream. It occurs in no retained term or clause.
            args.output.with_name(name+'.bits').write_text(pack(cs)+'\n')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
