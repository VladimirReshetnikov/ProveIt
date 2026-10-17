#!/usr/bin/env python3
"""A complete, deliberately simple finite-clause refutation reference.

Input terms are '?variable' or ['function', *arguments].  This program is
not a small Turing-machine compiler.  Its unbounded search semidecides
inconsistency of a finite first-order clause set with nonempty domain.
Native equality is handled by an explicit finite equality axiomatization.
Every reported refutation is an independently checkable ground-resolution
certificate.  No call to a SAT/SMT solver is made.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def freeze(t):
    if isinstance(t, str):
        if not t.startswith('?') or len(t) == 1:
            raise ValueError('Variables must start with ?')
        return t
    if not isinstance(t, (list, tuple)) or not t or not isinstance(t[0], str):
        raise ValueError('Malformed term')
    return (t[0], *(freeze(x) for x in t[1:]))


def thaw(t):
    return t if isinstance(t, str) else [t[0], *(thaw(x) for x in t[1:])]


def variables(t):
    if isinstance(t, str):
        return {t}
    return set().union(*(variables(x) for x in t[1:])) if len(t) > 1 else set()


def subst(t, sigma):
    if isinstance(t, str):
        return sigma[t]
    return (t[0], *(subst(x, sigma) for x in t[1:]))


def atom_key(atom):
    return repr(atom)


def lit_json(lit):
    sign, atom = lit
    return {'positive': sign, 'predicate': atom[0], 'args': [thaw(t) for t in atom[1:]]}


def clause_json(c):
    return [lit_json(lit) for lit in sorted(c, key=repr)]


def parse_literal(obj):
    if set(obj) != {'positive', 'predicate', 'args'} or type(obj['positive']) is not bool:
        raise ValueError('Malformed literal')
    if not isinstance(obj['predicate'], str) or not isinstance(obj['args'], list):
        raise ValueError('Malformed atom')
    return obj['positive'], (obj['predicate'], *(freeze(t) for t in obj['args']))


def parse_clause(obj):
    if not isinstance(obj, list):
        raise ValueError('A clause must be a list')
    return frozenset(parse_literal(x) for x in obj)


def clause_variables(c):
    return set().union(*(variables(t) for _, atom in c for t in atom[1:])) if c else set()


def tautology(c):
    return any((not sign, atom) in c for sign, atom in c)


def validate_term(t, functions, ground=False):
    if isinstance(t, str):
        if ground:
            raise ValueError('A ground term was required')
        return
    if t[0] not in functions or len(t)-1 != functions[t[0]]:
        raise ValueError('Unknown function or incorrect arity: ' + str(t[0]))
    for arg in t[1:]:
        validate_term(arg, functions, ground)


def validate_clause(c, functions, predicates, ground=False):
    for _, atom in c:
        if atom[0] not in predicates or len(atom)-1 != predicates[atom[0]]:
            raise ValueError('Unknown predicate or incorrect arity: ' + str(atom[0]))
        for t in atom[1:]:
            validate_term(t, functions, ground)


def equality_axioms(functions, predicates):
    """Native equality is replaced by an ordinary binary congruence predicate.

    Quotienting any model of these axioms gives a genuine equality model.
    Predicate congruence in the reverse direction follows by symmetry.
    """
    if 'eq' not in predicates:
        return []
    if predicates['eq'] != 2:
        raise ValueError('eq must be binary')
    def eq(x, y, positive=True):
        return {'positive': positive, 'predicate': 'eq', 'args': [x, y]}
    rows = [
        {'name': '$eq_reflexive', 'literals': [eq('?x', '?x')]},
        {'name': '$eq_symmetric', 'literals': [eq('?x', '?y', False), eq('?y', '?x')]},
        {'name': '$eq_transitive', 'literals': [eq('?x', '?y', False), eq('?y', '?z', False), eq('?x', '?z')]},
    ]
    for f, n in sorted(functions.items()):
        if n:
            xs, ys = [f'?x{i}' for i in range(n)], [f'?y{i}' for i in range(n)]
            rows.append({'name': '$eq_function_'+f,
                'literals': [eq(x,y,False) for x,y in zip(xs,ys)] + [eq([f,*xs],[f,*ys])]})
    for p, n in sorted(predicates.items()):
        if p != 'eq' and n:
            xs, ys = [f'?x{i}' for i in range(n)], [f'?y{i}' for i in range(n)]
            rows.append({'name': '$eq_predicate_'+p,
                'literals': [eq(x,y,False) for x,y in zip(xs,ys)] + [
                    {'positive':False,'predicate':p,'args':xs},
                    {'positive':True,'predicate':p,'args':ys}]})
    return rows


def load_kernel(kernel, add_equality=True):
    fs, ps = dict(kernel['functions']), dict(kernel['predicates'])
    if any(type(n) is not int or n < 0 for n in [*fs.values(),*ps.values()]):
        raise ValueError('Arities must be nonnegative integers')
    if not any(n == 0 for n in fs.values()):
        name = '$inhabitant'
        while name in fs:
            name += '_'
        fs[name] = 0
    rows = list(kernel['clauses'])
    if add_equality:
        rows += equality_axioms(fs,ps)
    axioms = {}
    for row in rows:
        if row['name'] in axioms:
            raise ValueError('Repeated axiom name')
        c = parse_clause(row['literals'])
        validate_clause(c,fs,ps)
        axioms[row['name']] = c
    return fs, ps, axioms


def ground_terms(functions, depth):
    """All terms of height <= depth, including a constant in every stage."""
    terms = {(f,) for f,n in functions.items() if n == 0}
    for _ in range(depth):
        previous = sorted(terms, key=repr)
        for f,n in sorted(functions.items()):
            if n:
                terms.update((f,*args) for args in itertools.product(previous,repeat=n))
    return sorted(terms,key=repr)


class Saturator:
    def __init__(self):
        self.clauses = []
        self.nodes = []
        self.index = {}
        self.pending = 0
        self.empty = None

    def add(self, clause, node):
        if tautology(clause) or clause in self.index:
            return
        i = len(self.clauses)
        self.index[clause] = i
        self.clauses.append(clause)
        self.nodes.append(dict(node,clause=clause_json(clause)))
        if not clause:
            self.empty = i

    def saturate(self):
        # Every unordered pair is processed when its later member is dequeued.
        # New resolvents are appended, so every finite stage terminates: only
        # finitely many clauses exist over that stage's finite atom vocabulary.
        while self.pending < len(self.clauses) and self.empty is None:
            i = self.pending
            self.pending += 1
            a = self.clauses[i]
            for j in range(i):
                b = self.clauses[j]
                for sign, atom in sorted(a,key=repr):
                    if (not sign,atom) in b:
                        resolvent = (a-{(sign,atom)}) | (b-{(not sign,atom)})
                        self.add(resolvent, {'kind':'resolve','parents':[i,j],
                            'pivot': {'predicate':atom[0],'args':[thaw(t) for t in atom[1:]]}})
                        if self.empty is not None:
                            return

    def certificate(self):
        if self.empty is None:
            return None
        # Keep only ancestors of the empty clause; provenance can otherwise
        # dwarf a short refutation. Every parent precedes its child.
        needed = set()
        def visit(i):
            if i in needed:
                return
            needed.add(i)
            for p in self.nodes[i].get('parents',[]):
                visit(p)
        visit(self.empty)
        order = sorted(needed)
        ren = {old:new for new,old in enumerate(order)}
        out = []
        for i in order:
            n = dict(self.nodes[i])
            if 'parents' in n:
                n['parents'] = [ren[p] for p in n['parents']]
            out.append(n)
        return {'format':'ground-resolution-v1','nodes':out,'conclusion':ren[self.empty]}


def refute(kernel, max_depth=None, instance_cap=None):
    fs,ps,axioms = load_kernel(kernel)
    sat = Saturator()
    seen = set()
    instance_count = 0
    depth = 0
    while max_depth is None or depth <= max_depth:
        terms = ground_terms(fs,depth)
        for name,c in sorted(axioms.items()):
            vs = sorted(clause_variables(c))
            for values in itertools.product(terms,repeat=len(vs)):
                key = (name,values)
                if key in seen:
                    continue
                if instance_cap is not None and instance_count >= instance_cap:
                    return {'status':'instance_cap','depth':depth,'instances':instance_count,'certificate':None}
                seen.add(key)
                instance_count += 1
                sigma = dict(zip(vs,values))
                ci = frozenset((s,(a[0],*(subst(t,sigma) for t in a[1:]))) for s,a in c)
                sat.add(ci,{'kind':'instance','axiom':name,
                           'substitution':{v:thaw(t) for v,t in sigma.items()}})
        sat.saturate()
        cert = sat.certificate()
        if cert is not None:
            verify_certificate(kernel,cert)
            return {'status':'refuted','depth':depth,'instances':instance_count,
                    'saturated_clauses':len(sat.clauses),'certificate':cert}
        depth += 1
    return {'status':'depth_limit','depth':max_depth,'instances':instance_count,
            'saturated_clauses':len(sat.clauses),'certificate':None}


def verify_certificate(kernel, certificate):
    """Independent of search state, clause indexing, and saturation order."""
    fs,ps,axioms = load_kernel(kernel)
    if certificate.get('format') != 'ground-resolution-v1':
        raise ValueError('Unsupported certificate format')
    proved = []
    for i,node in enumerate(certificate['nodes']):
        claimed = parse_clause(node['clause'])
        validate_clause(claimed,fs,ps,ground=True)
        if node['kind'] == 'instance':
            if node['axiom'] not in axioms:
                raise ValueError('Unknown axiom')
            source = axioms[node['axiom']]
            sigma = {v:freeze(t) for v,t in node['substitution'].items()}
            if set(sigma) != clause_variables(source):
                raise ValueError('Incomplete or extraneous substitution')
            for t in sigma.values():
                validate_term(t,fs,ground=True)
            actual = frozenset((s,(a[0],*(subst(t,sigma) for t in a[1:]))) for s,a in source)
            if actual != claimed:
                raise ValueError('Incorrect axiom instance')
        elif node['kind'] == 'resolve':
            parents = node.get('parents')
            if not isinstance(parents,list) or len(parents)!=2 or any(type(p) is not int or p < 0 or p >= i for p in parents):
                raise ValueError('Invalid parent index')
            a,b = [proved[p] for p in parents]
            p = node['pivot']
            atom = (p['predicate'],*(freeze(t) for t in p['args']))
            valid = False
            for sign in (False,True):
                if (sign,atom) in a and (not sign,atom) in b:
                    if (a-{(sign,atom)}) | (b-{(not sign,atom)}) == claimed:
                        valid = True
            if not valid:
                raise ValueError('Incorrect ground resolution')
        else:
            raise ValueError('Unknown proof command')
        proved.append(claimed)
    conclusion = certificate.get('conclusion')
    if type(conclusion) is not int or not (0 <= conclusion < len(proved)) or proved[conclusion]:
        raise ValueError('The conclusion is not the empty clause')
    return {'verified':True,'nodes':len(proved),'conclusion':conclusion}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('kernel',type=Path)
    p.add_argument('--certificate',type=Path)
    p.add_argument('--max-depth',type=int)
    p.add_argument('--instance-cap',type=int)
    p.add_argument('--output',type=Path,required=True)
    a = p.parse_args()
    k = json.loads(a.kernel.read_text())
    if a.certificate:
        result = verify_certificate(k,json.loads(a.certificate.read_text()))
    else:
        result = refute(k,a.max_depth,a.instance_cap)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({x:y for x,y in result.items() if x!='certificate'},sort_keys=True))


if __name__ == '__main__':
    main()
