#!/usr/bin/env python3
"""Independent counts for emitted ground/template codec artifacts.

This imports neither codec nor its metric functions.  Optional source44
verification imports the two pinned primary files only to regenerate their
original literal clause lists; it never needs them for the delivered codecs.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def nodes(term):
    return 1 if isinstance(term, str) else 1 + sum(map(nodes, term[1:]))


def depth(term):
    return 0 if isinstance(term, str) or len(term) == 1 else 1 + max(map(depth, term[1:]))


def variables(term):
    return {term} if isinstance(term, str) else set().union(*(variables(x) for x in term[1:]))


def clause_variables(clause):
    return sorted(set().union(*(variables(t) for literal in clause for t in literal[2:])))


def transform(term, environment):
    return environment[term] if isinstance(term, str) else (term[0],) + tuple(
        transform(x, environment) for x in term[1:])


def renaming(clause, environment):
    return tuple((s, p, transform(a, environment), transform(b, environment))
                 for s, p, a, b in clause)


def constructor_terms(clauses):
    result = set()

    def visit(t):
        if isinstance(t, str) or len(t) == 1:
            return
        result.add(t)
        for child in t[1:]:
            visit(child)

    for clause in clauses:
        for literal in clause:
            visit(literal[2]); visit(literal[3])
    return sorted(result, key=lambda t: (depth(t), repr(t)))


def bits_to_address(count):
    assert count > 0
    return (count - 1).bit_length()


def gamma_length(value):
    return 2 * value.bit_length() - 1


def template_counts(artifact):
    clauses = freeze(artifact['renamed_clauses'])
    constants = artifact.get('constants', ['d'])
    variable_slots = artifact.get('variable_slots', 6)
    bases = variable_slots + len(constants)
    opcode_width = bits_to_address(bases + len(artifact['functions']))
    literals = sum(map(len, clauses))
    tree_nodes = sum(nodes(t) for c in clauses for lit in c for t in lit[2:])
    controls = 3 * len(clauses) + 3 * literals + 3
    constructors = constructor_terms(clauses)
    dag_header = gamma_length(len(constructors) + 1)
    dag_dictionary = sum(opcode_width + (len(t) - 1) * bits_to_address(bases + i)
                         for i, t in enumerate(constructors))
    dag_body = controls + 2 * literals * bits_to_address(bases + len(constructors))

    function_index = {name: bases + i for i, (name, _) in enumerate(artifact['functions'])}
    escape_tag = (1 << opcode_width) - 1
    macros = freeze(artifact['macro_trees'])
    known = set()

    def cost(t):
        if isinstance(t, str) or len(t) == 1:
            return opcode_width
        expanded = opcode_width + int(function_index[t[0]] == escape_tag) + sum(map(cost, t[1:]))
        if t in known:
            return min(expanded, opcode_width + 1 + bits_to_address(len(known)))
        return expanded

    grammar_dictionary = 0
    for macro in macros:
        assert macro not in known
        grammar_dictionary += cost(macro)
        known.add(macro)
    grammar_header = gamma_length(len(macros) + 1)
    grammar_body = controls + sum(cost(t) for c in clauses for lit in c for t in lit[2:])
    return dict(flat_bits=controls + opcode_width * tree_nodes,
                dag_bits=dag_header + dag_dictionary + dag_body,
                grammar_bits=grammar_header + grammar_dictionary + grammar_body,
                dag_parts=[dag_header, dag_dictionary, dag_body],
                grammar_parts=[grammar_header, grammar_dictionary, grammar_body],
                known_constant_count=len(constants), known_variable_slots=variable_slots,
                term_opcode_width=opcode_width)


def grounding_counts(clauses, frontier=None, constants=('d',)):
    symbols = ['V', 'C', 'I', 'A', 'U', 'F']
    tags = {s: i for i, s in enumerate(symbols)}

    def cantor_pair(a, b):
        return (a + b) * (a + b + 1) // 2 + b

    def number(t):
        if len(t) == 1:
            return constants.index(t[0])
        children = [number(x) for x in t[1:]]
        packed = children.pop()
        while children:
            packed = cantor_pair(children.pop(), packed)
        return len(constants) + tags[t[0]] + 8 * packed

    frontier = frontier or [('d',), ('V', ('d',), ('d',))]
    atoms = set()
    clause_count = endpoints = max_nodes = max_depth = max_cantor_bits = 0
    for clause in clauses:
        names = clause_variables(clause)
        for values in product(frontier, repeat=len(names)):
            environment = dict(zip(names, values))
            clause_count += 1
            for _, predicate, a, b in clause:
                a, b = transform(a, environment), transform(b, environment)
                atoms.add((predicate, a, b))
                for term in (a, b):
                    endpoints += 1
                    max_nodes = max(max_nodes, nodes(term))
                    max_depth = max(max_depth, depth(term))
                    max_cantor_bits = max(max_cantor_bits, number(term).bit_length())
    return dict(ground_clauses=clause_count, ground_atoms=len(atoms),
                checked_endpoint_occurrences=endpoints,
                maximum_endpoint_tree_nodes=max_nodes, maximum_endpoint_depth=max_depth,
                maximum_prefix_word_bits=3 * max_nodes,
                maximum_integer_name_bits_with_leading_one=3 * max_nodes + 1,
                maximum_cantor_endpoint_bits=max_cantor_bits)


def verify_boolean_controls(source, reported):
    result = {}
    for base in ('FC13', 'FC14'):
        for suffix in ('_native', '_complete'):
            old = source[base + 'S' + suffix]
            new = source[base + 'B' + suffix]
            assert len(old) == len(new)
            assert old[:12] == new[:12] and old[13:] == new[13:]
            assert old[12][:-1] == new[12][:-1]
            sign, predicate, assignment, closure = old[12][-1]
            assert (sign, predicate, assignment) == new[12][-1][:3]
            assert closure[0] == 'I'
            locally_bounded, hull = closure[1:]
            assert hull[0] == 'I' and hull[2] == ('d',)
            universal = hull[1]
            assert universal[0] == 'U'
            selector, double_negative = universal[1:]
            assert double_negative[0] == 'I' and double_negative[2] == ('d',)
            negative = double_negative[1]
            assert negative[0] == 'I' and negative[2] == ('d',)
            inner = negative[1]
            expected = ('I', locally_bounded, ('I', ('U', selector, inner), ('d',)))
            assert new[12][-1][3] == expected
            count_old = sum(nodes(t) for c in old for lit in c for t in lit[2:])
            count_new = sum(nodes(t) for c in new for lit in c for t in lit[2:])
            assert count_old - count_new == 4
            actual = dict(clauses=len(new), literals=sum(map(len, new)), term_nodes=count_new,
                          max_term_depth=max(depth(t) for c in new for lit in c for t in lit[2:]),
                          max_variables=max(map(lambda c: len(clause_variables(c)), new)))
            actual['bits'] = 3 * actual['clauses'] + 3 * actual['literals'] + 4 * count_new + 3
            name = base + 'B' + suffix
            for key, value in actual.items():
                assert reported['metrics'][name][key] == value
            result[name] = actual
    return result


def replace_ground_term(clauses, old, new):
    def replace(t):
        if t == old:
            return new
        return t if isinstance(t, str) else (t[0],) + tuple(replace(x) for x in t[1:])
    return tuple(tuple((s, p, replace(a), replace(b)) for s, p, a, b in clause)
                 for clause in clauses)


def verify_named_controls(source, data):
    counts = {}
    for name, reported in data['metrics'].items():
        native = name.endswith('_native')
        old_name = ('FC13B' if name.startswith('FC14') else 'FC14B') + '_native'
        old = source[old_name]
        translated = replace_ground_term(old, ('I', ('d',), ('d',)), ('q',))
        expected_unit = ((True, 'Eq', ('q',), ('I', ('d',), ('d',))),) if 'Qd_' in name else (
            (True, 'Inc', 's', ('q',)),)
        expected_prefix = translated + (expected_unit,)
        actual = source[name]
        assert actual[:len(expected_prefix)] == expected_prefix
        old_complete = source[old_name.replace('_native', '_complete')]
        expected_tail = () if native else old_complete[len(old):]
        assert actual[len(expected_prefix):] == expected_tail
        literal_count = sum(map(len, actual))
        node_count = sum(nodes(t) for c in actual for lit in c for t in lit[2:])
        metrics = dict(clauses=len(actual), literals=literal_count, term_nodes=node_count,
                       max_term_depth=max(depth(t) for c in actual for lit in c for t in lit[2:]),
                       max_variables=max(len(clause_variables(c)) for c in actual),
                       flat_bits=3 * len(actual) + 3 * literal_count + 4 * node_count + 3)
        for key, value in metrics.items():
            assert reported[key] == value
        counts[name] = metrics
    return counts


def verify_channel_controls(source, data, directory):
    d, q = ('d',), ('q',)

    def pair(a, b):
        return ('C', ('C', d, d, a), q, b)

    tags = {'I': pair(d, d), 'A': pair(d, q), 'U': pair(q, d)}

    def convert(t):
        if isinstance(t, str) or len(t) == 1:
            return t
        children = tuple(map(convert, t[1:]))
        if t[0] in tags:
            return ('V', ('F', pair(tags[t[0]], pair(*children)), d), d)
        return (t[0],) + children

    result = {}
    for label, name in (('raw', 'FC14Q'), ('extensional', 'FC15Q')):
        original = source[name + '_native']
        original_complete = source[name + '_complete']
        changed = tuple(tuple((s, p, convert(a), convert(b)) for s, p, a, b in c) for c in original)
        retained_equality = []
        for clause in original_complete[len(original):]:
            _, predicate, left, right = clause[-1]
            if predicate == 'Eq' and not isinstance(left, str) and left[0] in tags:
                assert right[0] == left[0]
                continue
            retained_equality.append(clause)
        assert len(retained_equality) == 7
        for complete in (False, True):
            key = 'three_function_' + label + ('_complete' if complete else '_native')
            expected = changed + (tuple(retained_equality) if complete else ())
            actual = freeze(json.loads((directory / (key + '.json')).read_text()))
            assert actual == expected
            node_count = sum(nodes(t) for c in actual for lit in c for t in lit[2:])
            literal_count = sum(map(len, actual))
            metrics = dict(clauses=len(actual), literals=literal_count, term_nodes=node_count,
                           depth=max(depth(t) for c in actual for lit in c for t in lit[2:]),
                           flat_bits=3 * len(actual) + 3 * literal_count + 4 * node_count + 3)
            for field, value in metrics.items():
                assert data['metrics'][key][field] == value
            for suffix, field in (('.bits', 'flat_bits'), ('.grammar.bits', 'lexical_grammar_bits')):
                payload = (directory / (key + suffix)).read_text().strip()
                assert set(payload) <= {'0', '1'}
                assert len(payload) == data['metrics'][key][field]
                metrics[field] = len(payload)
            result[key] = metrics
    return result


def verify_source44(snapshot, root):
    for path, digest in snapshot['source_SHA256'].items():
        assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest

    def module(name, path):
        spec = importlib.util.spec_from_file_location(name, path)
        mod = importlib.util.module_from_spec(spec)
        sys.modules[name] = mod
        spec.loader.exec_module(mod)
        return mod

    old_ground = sys.modules.get('ground_kernel')
    try:
        g = module('ground_kernel', root / 'code/44-nine-code-ground_kernel.py')
        e = module('codec_audit_source44_extensional', root / 'code/44-nine-code-coded_extensional.py')
        native = g.source_clauses(False, True)
        fresh = dict(FC15star_native=native,
                     FC15star_complete=native + g.equality_clauses(False, g.signature(False, True)),
                     FC16star_native=e.native_clauses(), FC16star_complete=e.full_clauses())
        assert json.loads(json.dumps(g.signature(False, True))) == snapshot['functions']
        assert g.PREDICATES == snapshot['predicates']
        for name, clauses in fresh.items():
            assert json.loads(json.dumps(clauses)) == snapshot['theories'][name]['clauses']
    finally:
        if old_ground is None:
            del sys.modules['ground_kernel']
        else:
            sys.modules['ground_kernel'] = old_ground
    return dict(pinned_hashes_match=True, four_literal_clause_snapshots_match=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--formalisms', type=Path, required=True)
    parser.add_argument('--source44-root', type=Path,
                        help='Optional ProveIt zfc-closure-kernels directory')
    parser.add_argument('--output', type=Path, default=Path('codec-review.json'))
    args = parser.parse_args()
    directory = args.formalisms
    snapshot = json.loads((directory / 'source44-encoding-snapshot.json').read_text())
    source = {name: freeze(data['clauses']) for name, data in snapshot['theories'].items()}
    for file in directory.glob('FC*.json'):
        if '__' not in file.name:
            payload = json.loads(file.read_text())
            if isinstance(payload, list):
                source[file.stem] = freeze(payload)
    reported = json.loads((directory / 'shared-template-results.json').read_text())['metrics']
    named_data = None
    if (directory / 'named-selector-results.json').exists():
        named_data = json.loads((directory / 'named-selector-results.json').read_text())
        for name, choices in named_data['shared_metrics'].items():
            for policy, record in choices.items():
                reported[name + '__' + policy] = record
        for name, data in named_data['source44_named_selector_controls'].items():
            old_name = name.split('_Qd_slots')[0]
            definition = (((True, 'Eq', ('q',), ('N', ('d',), ('d',))),),)
            source[name] = replace_ground_term(source[old_name], ('N', ('d',), ('d',)), ('q',)) + definition
            for policy, record in data['metrics'].items():
                reported[name + '__' + policy] = record
    counts = {}
    for key, stated in reported.items():
        artifact = json.loads((directory / (key + '.shared.json')).read_text())
        original = source[artifact['theory']]
        changed = freeze(artifact['renamed_clauses'])
        assert len(original) == len(changed) == len(artifact['variable_maps'])
        for old, new, mapping in zip(original, changed, artifact['variable_maps']):
            names = clause_variables(old)
            assert set(mapping) == set(names)
            assert set(mapping.values()) == {'v' + str(i) for i in range(len(names))}
            assert renaming(old, mapping) == new
        actual = template_counts(artifact)
        for kind in ('flat', 'dag', 'grammar'):
            assert actual[kind + '_bits'] == stated[kind + '_bits']
            if kind != 'flat':
                bits = (directory / (key + '.' + kind + '.bits')).read_text().strip()
                assert set(bits) <= {'0', '1'}
                assert len(bits) == actual[kind + '_bits']
                assert actual[kind + '_parts'] == [stated[kind][field] for field in
                                                   ('header_bits', 'dictionary_bits', 'clause_body_bits')]
        counts[key] = actual
    ground = {}
    linear = json.loads((directory / 'linear-ground-results.json').read_text())['comparison']
    for name, stated in linear.items():
        actual = grounding_counts(source[name + '_complete'])
        for key, value in actual.items():
            assert stated[key] == value
        ground[name] = actual
    boolean = None
    if (directory / 'boolean-class-results.json').exists():
        data = json.loads((directory / 'boolean-class-results.json').read_text())
        boolean = verify_boolean_controls(source, data)
        for name, stated in data['stage_one'].items():
            actual = grounding_counts(source[name + '_complete'])
            for key, value in actual.items():
                assert stated[key] == value
            ground[name] = actual
    named = verify_named_controls(source, named_data) if named_data else None
    if named_data:
        for name, comparisons in named_data['ground_comparisons'].items():
            for label, stated in comparisons.items():
                frontier = [('d',), ('q',)] if label == 'own_first_two_d_q' else [
                    ('d',), ('V', ('d',), ('d',))]
                actual = grounding_counts(source[name + '_complete'], frontier, ('d', 'q'))
                for key, value in actual.items():
                    assert stated[key] == value
                ground[name + '__' + label] = actual
    provenance = verify_source44(snapshot, args.source44_root) if args.source44_root else None
    channel = None
    if (directory / 'channel-collapse-results.json').exists():
        channel_data = json.loads((directory / 'channel-collapse-results.json').read_text())
        channel = verify_channel_controls(source, channel_data, directory)
    out = dict(status='PASS', codec_metric_functions_imported=False,
               shared_cases=len(counts), local_alpha_bijections_verified=True,
               independently_charged_counts=counts, independently_grounded_counts=ground,
               exact_boolean_control_changes=boolean, exact_named_selector_changes=named,
               exact_channel_control_changes=channel,
               source44_provenance=provenance)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', shared_cases=len(counts),
                          ground_cases=len(ground), source44_provenance=provenance)))


if __name__ == '__main__':
    main()
