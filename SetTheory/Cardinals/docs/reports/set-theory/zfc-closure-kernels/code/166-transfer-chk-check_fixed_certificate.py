#!/usr/bin/env python3
"""Independent fixed-certificate verifier, authored for the 7071e5041e review.

Reads JSON as data only. Does not import/execute any supplied packet code.
Terms are ordinary finite Python trees: nonnegative int = metavariable,
'T' = raw numerical zero, tuple(left,right) = numerical implication.
Only the sound identity I(0,0)=0 is normalized. No search or unification.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import sys

T = 'T'

class Invalid(ValueError):
    pass

def require(test, why):
    if not test:
        raise Invalid(why)

def object_without_duplicate_keys(pairs):
    d = {}
    for k, v in pairs:
        require(k not in d, 'duplicate JSON key: ' + k)
        d[k] = v
    return d

def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=object_without_duplicate_keys)

def integer(n):
    return type(n) is int and n >= 0

def implication(a, b):
    return T if a == T and b == T else (a, b)

def rho(a, b, c, u):
    return implication(implication(implication(c, u), a),
                       implication(implication(a, c), implication(b, c)))

def parts(t):
    if t == T:
        # EXACT equality of natural codes, not an assumed logical equivalence.
        return T, T
    require(type(t) is tuple and len(t) == 2, 'not an implication or zero')
    return t

def variable_set(t):
    out = set()
    stack = [t]
    # Shared Python tree identities avoid repeatedly traversing shared subtrees.
    seen = set()
    while stack:
        x = stack.pop()
        if type(x) is tuple:
            if id(x) in seen:
                continue
            seen.add(id(x)); stack.extend(x)
        elif integer(x):
            out.add(x)
        else:
            require(x == T, 'malformed internal term')
    return out

def substitute(term, env):
    require(variable_set(term) <= env.keys(), 'incomplete explicit substitution')
    memo = {}
    def visit(x):
        if integer(x):
            return env[x]  # Simultaneous: do not substitute inside the replacement.
        if x == T:
            return T
        if id(x) not in memo:
            memo[id(x)] = implication(visit(x[0]), visit(x[1]))
        return memo[id(x)]
    return visit(term)

def renaming(source, target):
    """Return and verify a BIJECTIVE variable renaming, not just a match."""
    forward, backward = {}, {}
    work = [(source, target)]
    seen = set()
    while work:
        a, b = work.pop()
        if integer(a):
            require(integer(b), 'renaming changes a variable into a nonvariable')
            require(a not in forward or forward[a] == b, 'inconsistent renaming')
            require(b not in backward or backward[b] == a, 'noninjective renaming')
            forward[a] = b; backward[b] = a
        elif a == T:
            require(b == T, 'renaming changes truth')
        else:
            require(type(b) is tuple, 'renaming changes implication')
            pair = (id(a), id(b))
            if pair not in seen:
                seen.add(pair)
                work.append((a[1], b[1])); work.append((a[0], b[0]))
    return forward

def subterm_path(a, u):
    """Shortest concrete left/right path witnessing U as a literal subterm of A."""
    level = [(a, [])]
    seen = set()
    while level:
        later = []
        for x, path in level:
            if x == u:
                return path
            if type(x) is tuple and id(x) not in seen:
                seen.add(id(x))
                later.extend([(x[0], path + [0]), (x[1], path + [1])])
        level = later
    raise Invalid('nonzero U has no literal subterm witness in A')

def print_term(t):
    if t == T:
        return 'T'
    if integer(t):
        return 'p' + str(t)
    return '(' + print_term(t[0]) + ' -> ' + print_term(t[1]) + ')'

def nested_term(x):
    if x == T:
        return T
    if integer(x):
        return x
    require(type(x) is list and len(x) == 2, 'invalid nested term')
    return implication(nested_term(x[0]), nested_term(x[1]))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def decode(data):
    if data.get('format') == 'term_dag_v1':
        table = data['term_table']
        require(type(table) is list, 'term_table not list')
        decoded = []
        for i, x in enumerate(table):
            if x == T:
                t = T
            elif type(x) is dict:
                require(set(x) == {'var'} and integer(x['var']), 'invalid variable')
                t = x['var']
            else:
                require(type(x) is list and len(x) == 2, 'invalid DAG term')
                require(all(integer(j) and j < i for j in x), 'cyclic/forward term reference')
                t = implication(decoded[x[0]], decoded[x[1]])
            decoded.append(t)
        def get(x):
            require(integer(x) and x < len(decoded), 'invalid term-table reference')
            return decoded[x]
        return get, len(table)
    require('format' not in data and 'term_table' not in data, 'unknown format')
    return nested_term, None


def expected_roots():
    p, q, r = 0, 1, 2
    i = implication
    return {
        'I': i(p, p),
        'K': i(p, i(q, p)),
        'P': i(i(i(p, q), p), p),
        'cd59': i(i(p, q), i(i(i(p, r), p), q)),
        'B': i(i(p, q), i(i(q, r), i(p, r))),
        'S': i(i(p, i(q, r)), i(i(p, q), i(p, r))),
        'rho8': rho(0, 1, 2, 3),
    }


def verify(data, full):
    get, table_size = decode(data)
    require(type(data.get('truth_code')) is int and data['truth_code'] == 0,
            'wrong declared truth code')
    require(data.get('implication_code') == 'I(a,b)=4*((a+b)*(a+b+1)//2+b)',
            'wrong declared implication code')
    proof, rules = [], Counter()
    leaf_witnesses, rename_witnesses, zero_major_nodes = [], [], []
    decoded_rules = []
    dependencies = []
    nodes = data['nodes']
    require(type(nodes) is list, 'nodes not list')
    for number, node in enumerate(nodes):
        try:
            require(integer(node['id']) and node['id'] == number, 'node id mismatch')
            term, rule = get(node['term']), node['rule']
            kind = rule['kind']; rules[kind] += 1
            def parent(k):
                n = rule[k]
                require(integer(n) and n < number, 'cyclic/forward proof reference')
                return proof[n]
            def environment(k):
                raw = rule[k]
                require(type(raw) is dict, 'substitution not a dictionary')
                require(all(type(v) is str and v.isascii() and v.isdecimal()
                            and str(int(v)) == v for v in raw), 'invalid substitution variable')
                return {int(v): get(replacement) for v, replacement in raw.items()}
            dep = []
            decoded_rule = {'kind': kind}
            if kind == 'truth':
                require(set(rule) == {'kind'}, 'unexpected truth rule fields')
                require(term == T, 'truth leaf is not raw zero')
            elif kind == 'dominated_rho8':
                require(set(rule) == {'kind'}, 'unexpected axiom rule fields')
                left, right = parts(term)
                cu, a = parts(left)
                c, u = parts(cu)
                ac, bc = parts(right)
                a2, c2 = parts(ac)
                b, c3 = parts(bc)
                require(a == a2 and c == c2 == c3 and term == rho(a, b, c, u),
                        'not the exact rho8 shape')
                path = None if u == T else subterm_path(a, u)
                leaf_witnesses.append({'node': number, 'U_is_zero': u == T,
                                       'U_path_in_A': path, 'depth': None if path is None else len(path)})
            elif kind == 'substitution':
                require(set(rule) == {'kind', 'parent', 'substitution'}, 'unexpected substitution rule fields')
                source = parent('parent'); env = environment('substitution')
                require(substitute(source, env) == term, 'wrong explicit substitution result')
                dep = [rule['parent']]
                decoded_rule.update(parent=rule['parent'], substitution=env)
            elif kind in ('mp', 'mp_substitution'):
                fields = {'kind', 'major', 'minor'}
                if kind == 'mp_substitution':
                    fields |= {'major_substitution', 'minor_substitution'}
                require(set(rule) == fields, 'unexpected MP rule fields')
                major, minor = parent('major'), parent('minor')
                if kind == 'mp_substitution':
                    me, ne = environment('major_substitution'), environment('minor_substitution')
                    major, minor = substitute(major, me), substitute(minor, ne)
                    decoded_rule.update(major_substitution=me, minor_substitution=ne)
                ante, consequent = parts(major)
                require(ante == minor, 'MP antecedent mismatch')
                if kind == 'mp_substitution':
                    bijection = renaming(consequent, term)
                    rename_witnesses.append({'node': number, 'source_to_output_variable': bijection})
                else:
                    require(consequent == term, 'MP consequent mismatch')
                if major == T:
                    zero_major_nodes.append(number)
                dep = [rule['major'], rule['minor']]
                decoded_rule.update(major=rule['major'], minor=rule['minor'])
            else:
                raise Invalid('unsupported rule: ' + str(kind))
            proof.append(term); decoded_rules.append(decoded_rule); dependencies.append(dep)
        except Invalid as e:
            raise Invalid(f'node {number}: {e}') from e
    wanted = expected_roots()
    roots = data['roots'] if full else {'cd59': data['root']}
    require(set(roots) == (set(wanted) if full else {'cd59'}), 'unexpected root collection')
    root_results = {}
    for name, n in roots.items():
        require(integer(n) and n < len(proof), 'invalid root reference')
        # Require exact variable labels for advertised endpoints, stronger than alpha equality.
        require(proof[n] == wanted[name], 'incorrect exact root: ' + name)
        root_results[name] = {'node': n, 'term': print_term(proof[n])}
    final = roots['rho8' if full else 'cd59']
    ancestors, pending = set(), [final]
    while pending:
        n = pending.pop()
        if n not in ancestors:
            ancestors.add(n); pending.extend(dependencies[n])
    report = {
        'verified': True, 'proof_nodes': len(proof), 'term_table_nodes': table_size,
        'rule_counts': dict(rules), 'exact_roots': root_results,
        'root_ancestor_count': len(ancestors),
        'domination_zero_count': sum(x['U_is_zero'] for x in leaf_witnesses),
        'domination_depth_counts': dict(Counter(x['depth'] for x in leaf_witnesses if not x['U_is_zero'])),
        'maximum_subterm_depth': max(x['depth'] for x in leaf_witnesses if x['depth'] is not None),
        'MP_with_truth_as_major_nodes': zero_major_nodes,
        'explicit_renaming_count': len(rename_witnesses),
        'nonidentity_renaming_count': sum(any(int(k) != v for k, v in x['source_to_output_variable'].items()) for x in rename_witnesses),
    }
    return report, leaf_witnesses, rename_witnesses, proof, decoded_rules


def mutation_tests(full, cd):
    # Exercise major failure modes without changing input files.
    cases = []
    def fail(name, data, is_full):
        try:
            verify(data, is_full)
        except (Invalid, KeyError, IndexError, TypeError) as e:
            cases.append({'test': name, 'rejected': True, 'reason': str(e)})
        else:
            raise Invalid('negative test accepted: ' + name)
    clone = lambda d: json.loads(json.dumps(d))
    d = clone(full); d['roots']['rho8'] = 17; fail('wrong unrestricted root', d, True)
    d = clone(full); d['term_table'][2] = [2, 1]; fail('cyclic term reference', d, True)
    d = clone(full); d['nodes'][3]['rule']['major'] = 3; fail('cyclic proof reference', d, True)
    d = clone(full); del d['nodes'][3]['rule']['major_substitution']['0']; fail('missing substitution variable', d, True)
    d = clone(full); d['nodes'][11]['term'] = 0; fail('variable zero confused with truth zero', d, True)
    d = clone(cd); d['nodes'][0]['term'] = [[[0, 1], 3], [[3, 0], [2, 0]]]; fail('undominated but shaped rho8 leaf', d, False)
    d = clone(cd); d['nodes'][17]['term'] = [0, 1]; fail('nonbijective output renaming', d, False)
    require(substitute((0, 1), {0: 1, 1: 2}) == (1, 2), 'simultaneous-substitution self-test')
    require(implication(T, T) == T and implication(0, 0) != T, 'zero-normalization self-test')
    return cases


def main():
    input_dir, output_dir = map(Path, sys.argv[1:3])
    output_dir.mkdir(parents=True, exist_ok=True)
    full_path = input_dir / 'dominated_rho8_full_certificate.json'
    cd_path = input_dir / 'cd59_certificate.json'
    full_data, cd_data = read_json(full_path), read_json(cd_path)
    full, fw, fr, fp, fpr = verify(full_data, True)
    cd, cw, cr, cp, cpr = verify(cd_data, False)
    require(fp[:58] == cp and fpr[:58] == cpr, 'cd59 is not an exact decoded prefix of full certificate')
    result = {
        'verdict': 'PASS', 'scope': 'Finite universal natural-code theorem only; no machine/compiler/startup claim.',
        'input_sha256': {p.name: sha(p) for p in [full_path, cd_path, input_dir / 'README.md']},
        'full_certificate': full, 'cd59_certificate': cd,
        'cd59_exact_decoded_prefix': True,
        'negative_tests': mutation_tests(full_data, cd_data),
        'normalization': 'Only I(T,T)=T; T denotes natural zero, integer leaf 0 denotes a variable.',
        'substitution_semantics': 'Complete simultaneous substitutions instantiate universally quantified schemas; not a new numerical inference rule.',
        'checker_sha256': sha(Path(__file__)),
    }
    (output_dir / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    (output_dir / 'domination_witnesses.json').write_text(json.dumps({'full': fw, 'cd59': cw}, indent=2) + '\n')
    (output_dir / 'renaming_witnesses.json').write_text(json.dumps({'full': fr, 'cd59': cr}, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
