#!/usr/bin/env python3
"""Independent finite regressions for the clausal trace reference pipeline.

These are diagnostics, not a formal proof or a consistency computation.
Finite source semantics and Skolem-expansion semantics are enumerated by
separate code, and propositional refutations are compared with truth tables.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

import clausal_trace as ct
import qpsc_syntax as s


def require(condition, message):
    if not condition:
        raise ValueError(message)


def ground_value(term, variables, functions, size):
    if type(term) is int:
        return variables[term]
    index = 0
    for child in term[1:]:
        index = size*index + ground_value(child, variables, functions, size)
    return functions[term[0]][index]


def clause_model(package, members, functions):
    size = len(members)
    for clause, variables in zip(package.clauses, package.clause_variables, strict=True):
        for values in itertools.product(range(size), repeat=len(variables)):
            env = dict(zip(variables, values, strict=True))
            satisfied = False
            for positive, a, b in clause:
                a = ground_value(a, env, functions, size)
                b = ground_value(b, env, functions, size)
                if positive == bool(members[b] & (1 << a)):
                    satisfied = True
                    break
            if not satisfied:
                return False
    return True


def has_skolem_expansion(package, members):
    size = len(members)
    symbols = list(package.signature)[1:]
    lengths = [size**package.signature[f] for f in symbols]
    for choices in itertools.product(range(size), repeat=sum(lengths)):
        functions, offset = {0: (0,)}, 0
        for symbol, length in zip(symbols, lengths, strict=True):
            functions[symbol] = choices[offset:offset+length]
            offset += length
        if clause_model(package, members, functions):
            return True
    return False


def semantic_checks():
    p = lambda x: s.E(x, x)
    samples = [s.T, s.B,
        s.A(0, s.Ex(1, s.E(0, 1))),
        s.Ex(1, s.A(0, s.E(0, 1))),
        s.A(0, s.Ex(1, s.And(s.E(0, 1), s.N(s.E(1, 0))))),
        s.And(s.Ex(0, p(0)), s.Ex(0, s.N(p(0)))),
        s.A(0, s.Ex(0, p(0))),
        s.Or(s.A(0, p(0)), s.Ex(0, s.N(p(0)))),
        s.I(s.A(0, p(0)), s.Ex(0, p(0))),
        s.N(s.A(0, s.A(1, s.I(s.E(0, 1), s.E(1, 0))))),
    ]
    for n in range(80):
        f = s.parse(ct.decode_matrix(n))
        closed = s.All(sorted(s.free(f)), f)
        samples.extend((closed, s.N(closed)))
    samples = list(dict.fromkeys(samples))
    count = 0
    for formula in samples:
        package = ct.Clauses().add(formula)
        for size in (1, 2):
            bits = sum(size**arity for f, arity in package.signature.items() if f != 0)
            require(bits <= 12, 'Unexpectedly expensive finite semantic test')
            for members in itertools.product(range(1 << size), repeat=size):
                original = s.evaluate(formula, members, {})
                expanded = has_skolem_expansion(package, members)
                require(original == expanded, 'Finite Skolem semantics disagree')
                count += 1
    dependent = ct.Clauses().add(s.A(0, s.Ex(1, s.E(0, 1))))
    constant = ct.Clauses().add(s.Ex(1, s.A(0, s.E(0, 1))))
    require(dependent.signature[1] == 1 and constant.signature[1] == 0,
            'Skolem dependencies were lost')
    fresh = ct.Clauses().add(s.And(s.Ex(0, p(0)), s.Ex(0, s.N(p(0)))))
    require(fresh.signature == {0: 0, 1: 0, 2: 0}, 'Existential witnesses were aliased')
    return {'closed_formulas': len(samples), 'finite_structure_comparisons': count,
            'universal_dependencies_checked': True, 'distinct_witness_symbols_checked': True}


def make_trace(package, instances):
    """Untrusted fixed-order exhaustive propositional search, only for tests."""
    def visit(depth, trail):
        if trail:
            for i, previous in enumerate(trail[:-1]):
                if ct.complementary(previous, trail[-1]):
                    return [['c', i]]
        if depth == len(instances):
            return None
        source, arguments = instances[depth]
        clause = package.instance(source, arguments)
        result = [['e', source, arguments]]
        for literal in clause:
            branch = visit(depth+1, trail+(literal,))
            if branch is None:
                return None
            result += branch
        return result
    return visit(0, ())


def propositional_checks():
    all_clauses = []
    for signs in itertools.product((-1, 0, 1), repeat=3):
        all_clauses.append(tuple((sign == 1, (i,), (i,))
                                 for i, sign in enumerate(signs) if sign))
    tested = accepted = 0
    for length in range(5):
        for chosen in itertools.combinations(range(len(all_clauses)), length):
            package = ct.Clauses(signature={0: 0, 1: 0, 2: 0},
                                 clauses=[all_clauses[i] for i in chosen],
                                 clause_variables=[()]*length)
            sat = any(all(any(sign == bool(mask & (1 << a[0])) for sign, a, b in clause)
                          for clause in package.clauses) for mask in range(8))
            trace = make_trace(package, [(i, []) for i in range(length)])
            require((trace is None) == sat, 'Generated tableau disagrees with truth table')
            if trace is not None:
                require(ct.check_trace(package, trace)['valid'], 'Valid trace rejected')
                accepted += 1
            tested += 1
    return {'CNFs_tested': tested, 'valid_refutations_checked': accepted,
            'independent_truth_table_comparison': True}


def source_and_negative_checks():
    p = lambda x: s.E(x, x)
    package = ct.Clauses().add(s.A(0, p(0))).add(s.Ex(0, s.N(p(0))))
    instances = [(0, [[1]]), (1, [])]
    trace = make_trace(package, instances)
    require(ct.check_trace(package, trace)['valid'], 'First-order example failed')
    bad = [[], trace[:-1], trace + [['c', 0]],
           [['e', 0, [[0]]], ['e', 1, []], ['c', 0]],
           [['e', 0, [[2]]]], [['e', 0, [[1, [0]]]]],
           [['e', True, [[1]]]], [['e', 0, [[False]]]],
           [['e', 0, []]], [['e', 0, [[1]]], ['c', 0]],
           [['e', 0, [[1]]], ['e', 1, []], ['c', True]],
           [['e', 0, [[1]]], ['e', 1, []], ['c', 2]],
           [['x', 0, []]], [0], [['c', -1]],
    ]
    for candidate in bad:
        try:
            ct.check_trace(package, candidate)
        except (ValueError, KeyError, IndexError):
            continue
        raise ValueError('Malformed or unsound trace was accepted')
    # An empty source clause closes even the empty initial branch.
    require(ct.check_trace(ct.Clauses().add(s.B), [['e', 0, []]])['valid'],
            'Empty clause did not close')
    # Symbols allocated by a later source sentence must never rename an earlier one.
    incremental = ct.Clauses().add(s.Ex(0, p(0)))
    prefix = list(incremental.clauses)
    incremental.add(s.Ex(0, s.N(p(0))))
    require(incremental.clauses[:len(prefix)] == prefix, 'Axiom prefixes are unstable')
    matrices = [ct.decode_matrix(i) for i in range(200)]
    actual = ct.compile_psc(matrices)
    require(all(set(v).issubset(range(actual.next_variable)) for v in actual.clause_variables),
            'Generated PSC source has an undefined variable')
    for c in ({'matrices': [], 'trace': [], 'theorem': ['B']},
              {'matrices': [], 'trace': [['e', 0, []]]}):
        try:
            ct.check_certificate(c)
        except ValueError:
            continue
        raise ValueError('Unauthorized certificate mode or source was accepted')
    return {'first_order_ground_refutation_checked': True,
            'malformed_traces_rejected': len(bad), 'empty_clause_checked': True,
            'stable_source_prefix_checked': True, 'PSC_matrices_clausified': len(matrices),
            'PSC_generated_clauses': len(actual.clauses),
            'PSC_Skolem_functions': len(actual.signature)-1,
            'PSC_maximum_Skolem_arity': max(actual.signature.values()),
            'no_theorem_mode': True}, trace


def codec_checks():
    for n in range(5000):
        require(ct.encode_certificate(ct.decode_certificate(n)) == n, 'Certificate codec mismatch')
        require(ct.encode_term(ct.decode_term(n)) == n, 'Term codec mismatch')
        require(ct.encode_matrix(ct.decode_matrix(n)) == n, 'Matrix codec mismatch')
    rejected = sum(not ct.accepts(n) for n in range(1000))
    require(rejected == 1000, 'Unexpected PSC refutation in the diagnostic prefix')
    return {'natural_roundtrips_each_codec': 5000, 'diagnostic_refutation_prefix': 1000,
            'finite_search_found_refutation': False}


def specialization_checks():
    """Negate and refute the precise cross-variable and diagonal theorems."""
    common = s.A(0, s.E(0, 2))
    cross = s.All([1, 2], s.I(common, s.E(1, 2)))
    diagonal = s.A(2, s.I(common, s.E(2, 2)))
    examples = []
    for name, theorem, expected, chosen in (
        ('cross_variable', cross,
         [((True, 0, (2,)),), ((False, (1,), (2,)),)], [1]),
        ('diagonal', diagonal,
         [((True, 0, (1,)),), ((False, (1,), (1,)),)], [1]),
    ):
        negated = s.N(theorem)
        package = ct.Clauses().add(negated)
        require(package.clauses == expected, 'Specialization clausification changed')
        trace = [['e', 0, [chosen]], ['e', 1, []], ['c', 0]]
        result = ct.check_trace(package, trace)
        require(result['valid'] and result['closed_branches'] == 1,
                'Specialization certificate failed')
        examples.append({'name': name, 'theorem': theorem, 'negated_source_sentence': negated,
                         'signature': package.signature, 'clauses': package.clauses,
                         'clause_variables': package.clause_variables,
                         'trace': trace, 'checked': result})
    # E is diagonal on {0,1}. The two quantifier orders have different truth values.
    dependent = s.A(0, s.Ex(1, s.E(0, 1)))
    constant = s.Ex(1, s.A(0, s.E(0, 1)))
    members = (1, 2)
    dpackage, cpackage = ct.Clauses().add(dependent), ct.Clauses().add(constant)
    functions = {0: (0,), 1: (0, 1)}
    require(s.evaluate(dependent, members, {}) and not s.evaluate(constant, members, {}),
            'Quantifier-order control has the wrong original semantics')
    require(clause_model(dpackage, members, functions), 'Unary witness did not work')
    require(has_skolem_expansion(dpackage, members) and not has_skolem_expansion(cpackage, members),
            'Dependent and constant Skolem witnesses were confused')
    controls = {'domain': [0, 1], 'membership_column_masks': members,
                'dependent_sentence': dependent, 'constant_sentence': constant,
                'dependent_signature': dpackage.signature, 'constant_signature': cpackage.signature,
                'dependent_function_interpretation': functions,
                'dependent_expansion_exists': True, 'constant_expansion_exists': False}
    artifact = {'scope': 'Generic first-order regression certificates; not PSC refutations.',
                'specialization_certificates': examples, 'Skolem_dependence_control': controls}
    evidence = {'cross_variable_certificate_checked': True,
                'diagonal_certificate_checked': True,
                'each_trace_extensions': 2, 'each_trace_closures': 1,
                'negated_cross_clauses': 'R(x,b), not R(a,b)',
                'negated_diagonal_clauses': 'R(x,b), not R(b,b)',
                'Skolem_dependence_diagonal_structure_checked': True}
    return evidence, artifact


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
                        help='Directory for result JSONs; defaults to this script directory')
    args = parser.parse_args()
    result = {'semantics': semantic_checks(), 'propositional': propositional_checks()}
    result['source_and_negative'], trace = source_and_negative_checks()
    result['codec'] = codec_checks()
    result['specialization'], specializations = specialization_checks()
    root = Path(__file__).resolve().parent
    output = args.output_dir.resolve() if args.output_dir else root
    output.mkdir(parents=True, exist_ok=True)
    result['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest()
                              for name in ('clausal_trace.py', 'qpsc_syntax.py', Path(__file__).name)}
    result['claim'] = 'Finite reference validation; no formal proof, no small binary TM count.'
    (output/'clausal_trace_results.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    (output/'synthetic_ground_refutation.json').write_text(json.dumps({
        'source_sentences': [['A', 0, ['E', 0, 0]],
                             ['I', ['A', 0, ['I', ['I', ['E', 0, 0], ['B']], ['B']]], ['B']]],
        'trace': trace,
        'scope': 'Synthetic generic-clause regression, not a PSC refutation'}, indent=2)+'\n')
    (output/'specialization_certificates.json').write_text(json.dumps(specializations, indent=2)+'\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
