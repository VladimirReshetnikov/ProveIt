#!/usr/bin/env python3
"""Finite assignment/class kernel for Con(ZFC): exact 28-clause payload.

Ordinary mathematical construction, not a verified compiler or state record.
The original 12 axioms and their consistency proof are in finite_kernel_notes.md.
The 28 universally closed clauses here include genuine first-order equality.
The small EUF checker below is a reference for finite *ground* clause sets,
not a claim that whole-kernel search has been feasibly run.

Run: python finite_assignment_kernel.py --out DIR
Only Python's standard library is needed.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path

# A variable is a one-item tuple. An application is (symbol,arg,...).
# Constants e and I are zero-argument applications, distinguished by signature.
SIG = {
    'e': 0, 'I': 0,
    'V': 2, 'C': 3, 'Pair': 2, 'Union': 1, 'Power': 1,
    'Nand': 2, 'Atom': 2, 'Exists': 2,
    'ExistsWitness': 3, 'ExtWitness': 2,
    'UnionWitness': 2, 'PowerWitness': 2,
    'Sep': 3, 'Collect': 3, 'CollectWitness': 4,
}
RELS = {'E': 2, 'eps': 2, '=': 2}

def app(symbol, *args): return (symbol, *args)
def var(name):
    assert name not in SIG
    return (name,)
def lit(positive, predicate, *args): return (positive, predicate, *args)
def pos(predicate, *args): return lit(True, predicate, *args)
def neg(predicate, *args): return lit(False, predicate, *args)

e, I = app('e'), app('I')
s,j,z,k,a,b,t,x,y = map(var, ('s','j','z','k','a','b','t','x','y'))
V=lambda p,q: app('V',p,q)
C=lambda p,q,r: app('C',p,q,r)
P=lambda p,q: app('Pair',p,q)
U=lambda p: app('Union',p)
W=lambda p: app('Power',p)

CLAUSES=[]
def clause(source, *literals):
    CLAUSES.append({'source': source, 'literals': tuple(literals)})

# A1: finite assignment update, all selectors in one common domain.
clause('A1.Change', pos('=', V(C(s,j,z),j),z))
clause('A1.Change', pos('=',k,j),pos('=',V(C(s,j,z),k),V(s,k)))
# A2: class NAND. Class codes need not be unique.
n=app('Nand',a,b)
clause('A2.NAND',neg('eps',s,n),neg('eps',s,a),neg('eps',s,b))
clause('A2.NAND',pos('eps',s,n),pos('eps',s,a))
clause('A2.NAND',pos('eps',s,n),pos('eps',s,b))
# A3: membership evaluated at two assignment coordinates.
m=app('Atom',j,k)
clause('A3.Atom',neg('eps',s,m),pos('E',V(s,j),V(s,k)))
clause('A3.Atom',pos('eps',s,m),neg('E',V(s,j),V(s,k)))
# A4: existential quantification of an assignment coordinate.
q=app('Exists',j,a); qw=app('ExistsWitness',j,a,s)
clause('A4.Exists',neg('eps',s,q),pos('eps',C(s,j,qw),a))
clause('A4.Exists',neg('eps',C(s,j,z),a),pos('eps',s,q))
# A5: empty object.
clause('A5.Empty',neg('E',x,e))
# A6: extensionality. Distinct objects have differing incoming profiles.
d=app('ExtWitness',a,b)
clause('A6.Ext',pos('=',a,b),pos('E',d,a),pos('E',d,b))
clause('A6.Ext',pos('=',a,b),neg('E',d,a),neg('E',d,b))
# The two preceding clauses express XOR: at least one membership and not both.
# A7: exact unordered pair.
p=P(a,b)
clause('A7.Pair',neg('E',x,p),pos('=',x,a),pos('=',x,b))
clause('A7.Pair',neg('=',x,a),pos('E',x,p))
clause('A7.Pair',neg('=',x,b),pos('E',x,p))
# A8: exact union.
uw=app('UnionWitness',a,x)
clause('A8.Union',neg('E',x,U(a)),pos('E',uw,a))
clause('A8.Union',neg('E',x,U(a)),pos('E',x,uw))
clause('A8.Union',neg('E',z,a),neg('E',x,z),pos('E',x,U(a)))
# A9: exact power set.
pw=app('PowerWitness',a,x)
clause('A9.Power',neg('E',x,W(a)),neg('E',z,x),pos('E',z,a))
clause('A9.Power',pos('E',x,W(a)),pos('E',pw,x))
clause('A9.Power',pos('E',x,W(a)),neg('E',pw,a))
# A10: ordinary successor Infinity; no appeal to an unproved weak-pair variant.
clause('A10.Infinity',pos('E',e,I))
clause('A10.Infinity',neg('E',x,I),pos('E',U(P(x,P(x,x))),I))
# A11: projection fused into Separation. b stores the fixed parameter values.
h=app('Sep',a,b,t); rx=C(b,e,x)
clause('A11.Sep',neg('E',x,h),pos('E',x,a))
clause('A11.Sep',neg('E',x,h),pos('eps',rx,t))
clause('A11.Sep',neg('E',x,a),neg('eps',rx,t),pos('E',x,h))
# A12: direct partial Collection. Witness omits antecedent-witness variable y.
B=app('Collect',a,b,t); f=app('CollectWitness',a,b,t,x)
rxy=C(C(b,e,x),I,y); rxf=C(C(b,e,x),I,f)
clause('A12.Collection',neg('E',x,a),neg('eps',rxy,t),pos('E',f,B))
clause('A12.Collection',neg('E',x,a),neg('eps',rxy,t),pos('eps',rxf,t))

def is_var(q): return len(q)==1 and q[0] not in SIG
def term_vars(q):
    return {q[0]} if is_var(q) else set().union(*(term_vars(v) for v in q[1:]))
def term_nodes(q): return 1+sum(map(term_nodes,q[1:]))
def term_depth(q): return 0 if len(q)==1 else 1+max(map(term_depth,q[1:]))
def show_term(q): return q[0] if len(q)==1 else q[0]+'('+','.join(map(show_term,q[1:]))+')'
def show_lit(l):
    p,r,*args=l
    body=(show_term(args[0])+' = '+show_term(args[1])) if r=='=' else r+'('+','.join(map(show_term,args))+')'
    return body if p else '~('+body+')'
def show_clause(c):
    vs=sorted(set().union(*(term_vars(q) for l in c['literals'] for q in l[2:])))
    return ('forall '+','.join(vs)+': ' if vs else '')+' | '.join(map(show_lit,c['literals']))
def subst_term(q, env): return env[q[0]] if is_var(q) else (q[0],*(subst_term(v,env) for v in q[1:]))
def instantiate(c, env): return tuple((l[0],l[1],*(subst_term(q,env) for q in l[2:])) for l in c['literals'])

def audit():
    def check(q):
        if is_var(q): return
        assert q[0] in SIG and len(q)-1==SIG[q[0]],q
        for child in q[1:]: check(child)
    for c in CLAUSES:
        assert c['literals']
        for l in c['literals']:
            assert type(l[0]) is bool and l[1] in RELS and len(l)-2==RELS[l[1]]
            for q in l[2:]: check(q)
    assert len(CLAUSES)==28
    assert len({c['source'] for c in CLAUSES})==12
    groups={}
    for c in CLAUSES: groups[c['source']]=groups.get(c['source'],0)+1
    # CollectWitness must depend on a,b,t,x, and must not depend on witness y.
    assert f==app('CollectWitness',a,b,t,x) and term_vars(f)=={'a','b','t','x'}
    assert qw==app('ExistsWitness',j,a,s)
    return {
        'status':'syntactic payload audit, not a formal proof or TM bound',
        'axioms':12,'clauses':len(CLAUSES),'clauses_by_axiom':groups,
        'constants':2,'proper_function_symbols':len(SIG)-2,
        'function_arity_histogram':{str(r):sum(v==r for v in SIG.values()) for r in range(5)},
        'relation_symbols_excluding_equality':2,
        'max_universal_variables_per_clause':max(len(set().union(*(term_vars(q) for l in c['literals'] for q in l[2:]))) for c in CLAUSES),
        'literal_occurrences':sum(len(c['literals']) for c in CLAUSES),
        'term_nodes_counting_occurrences':sum(term_nodes(q) for c in CLAUSES for l in c['literals'] for q in l[2:]),
        'max_term_depth':max(term_depth(q) for c in CLAUSES for l in c['literals'] for q in l[2:]),
    }

def subterms(q):
    yield q
    for a in q[1:]: yield from subterms(a)

def partitions(n):
    """All equivalence relations, canonical restricted-growth labels."""
    if n==0:
        yield (); return
    def rec(xs, high):
        if len(xs)==n:
            yield tuple(xs); return
        for value in range(high+2):
            xs.append(value)
            yield from rec(xs,max(high,value))
            xs.pop()
    yield from rec([0],0)

def ground_satisfiable(clauses):
    """Exact finite-ground satisfiability in equality + uninterpreted functions.

    Enumerates partitions of every ground subterm and all consistent predicate
    values. Term congruence and predicate congruence are enforced. This is
    deliberately unoptimized; it is only used on tiny diagnostic controls.
    """
    qs=sorted(set(q for c in clauses for l in c for a in l[2:] for q in subterms(a)),key=repr)
    if any(is_var(q) for q in qs): raise ValueError('ground clauses required')
    if not qs: qs=[e] # first-order domains are nonempty
    for part in partitions(len(qs)):
        classes=dict(zip(qs,part)); applications={}; good=True
        for q in qs:
            key=(q[0],*(classes[a] for a in q[1:]))
            if key in applications and applications[key]!=classes[q]:
                good=False; break
            applications[key]=classes[q]
        if not good: continue
        atoms=sorted({(l[1],*(classes[a] for a in l[2:])) for c in clauses for l in c if l[1]!='='})
        for bits in itertools.product((False,True),repeat=len(atoms)):
            valuation=dict(zip(atoms,bits))
            def value(l):
                b=(classes[l[2]]==classes[l[3]]) if l[1]=='=' else valuation[(l[1],*(classes[a] for a in l[2:]))]
                return b if l[0] else not b
            if all(any(map(value,c)) for c in clauses): return True
    return False

def enumerate_ground_terms():
    """Fair enumeration by increasing depth (potentially enormous layers)."""
    seen=set(); prior=[]
    for symbol, arity in SIG.items():
        if arity==0:
            q=app(symbol); seen.add(q); prior.append(q); yield q
    while True:
        current=[]
        for symbol, arity in SIG.items():
            if arity==0: continue
            for args in itertools.product(prior,repeat=arity):
                q=app(symbol,*args)
                if q not in seen:
                    seen.add(q); current.append(q); yield q
        if not current: return
        prior.extend(current)

def ground_stage(prefix_length):
    """All kernel instances over the requested finite ground-term prefix."""
    if prefix_length<1: raise ValueError('positive prefix length required')
    terms=list(itertools.islice(enumerate_ground_terms(),prefix_length))
    clauses=[]
    for c in CLAUSES:
        variables=sorted(set().union(*(term_vars(q) for l in c['literals'] for q in l[2:])))
        for values in itertools.product(terms,repeat=len(variables)):
            clauses.append(instantiate(c,dict(zip(variables,values))))
    return tuple(clauses)

def ideal_search():
    """The complete unbounded ideal search. NOT RUN by this artifact's CLI.

    Returns the first inconsistent ground stage, if any. This function is a
    mathematical executable specification, not a practical consistency test;
    even the first full stage makes the naive partition algorithm prohibitive.
    Host exceptions/resource exhaustion are not accepting outcomes.
    """
    for n in itertools.count(1):
        if not ground_satisfiable(ground_stage(n)): return n

def diagnostics():
    pe=P(e,e); pi=P(I,e)
    cases=[
        ('empty_ground_theory',(),True),
        ('empty_clause',((),),False),
        ('equality_reflexivity',((neg('=',e,e),),),False),
        ('distinct_constants',((neg('=',e,I),),),True),
        ('function_congruence',((pos('=',e,I),),(neg('=',pe,pi),)),False),
        ('predicate_congruence',((pos('=',e,I),),(pos('E',e,e),),(neg('E',I,e),)),False),
        ('cyclic_uninterpreted_function_allowed',((pos('=',pe,e),),),True),
    ]
    results=[]
    for name, clauses, expected in cases:
        got=ground_satisfiable(clauses)
        assert got==expected,(name,got,expected)
        results.append({'case':name,'satisfiable':got})
    # A5.Empty + A10.Infinity force e != I. These are genuine kernel instances.
    ce=instantiate(CLAUSES[9],{'x':I})
    ci=CLAUSES[21]['literals']
    assert not ground_satisfiable((ce,ci,(pos('=',e,I),)))
    results.append({'case':'empty_infinity_distinct_from_actual_rows','satisfiable_with_e_equals_I':False})
    # Extensional separating witness row pair has the exact XOR table.
    table=[]
    for eq,ma,mb in itertools.product((False,True),repeat=3):
        got=(eq or ma or mb) and (eq or not ma or not mb)
        expected=eq or (ma!=mb)
        assert got==expected
        table.append([eq,ma,mb,got])
    return {'tests':results,'extensionality_witness_truth_table':table,'whole_kernel_search_run':False}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    metrics=audit(); tests=diagnostics()
    payload={'signature':SIG,'relations':RELS,'universally_closed_clauses':CLAUSES}
    (args.out/'finite_kernel_clauses.json').write_text(json.dumps(payload,indent=2)+'\n')
    (args.out/'finite_kernel_clauses.txt').write_text('\n'.join(f'{i+1:02d} [{c["source"]}] {show_clause(c)}' for i,c in enumerate(CLAUSES))+'\n')
    (args.out/'finite_kernel_audit.json').write_text(json.dumps({'metrics':metrics,'diagnostics':tests},indent=2)+'\n')
    print(json.dumps({'metrics':metrics,'diagnostic_cases':len(tests['tests'])},indent=2))

if __name__=='__main__': main()
