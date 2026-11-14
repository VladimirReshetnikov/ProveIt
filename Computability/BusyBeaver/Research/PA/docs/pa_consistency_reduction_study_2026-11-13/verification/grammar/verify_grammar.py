#!/usr/bin/env python3
"""Check a feasible straight-line grammar witness, using Python's standard library.

This checks the exact macro word and a summed RHS binary cost of 67. It does
not check any optimizer's claimed bound, prove optimality, or certify a TM.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REFERENCE_SHA256 = 'ca78fcfb8394f09eea1ed0d2fdf8fbabd8b4f5ac524f742ba9c45f4b69c1915f'
COMMIT = '75a42a28ca818627f5a104fb0f0c7f7d02a52947'
MACROS = frozenset(('node65', 'node55', 'node58', 'node70', 'node49',
                    'node72', 'node75', 'node142', 'node150', 'node60', 'node61'))
INC = ('leaf', 'inc', 1)
BREAK = ('leaf', 'breakTo', 1)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, 'Duplicate JSON key: ' + key)
        out[key] = value
    return out


def read(path):
    raw = path.read_bytes()
    return raw, json.loads(raw, object_pairs_hook=unique_object)


def expand(document, field, binary):
    """Independently resolve an acyclic grammar, rejecting unused definitions."""
    require(isinstance(document, dict), 'Document must be an object')
    rules = document.get(field)
    root = document.get('root')
    require(isinstance(rules, dict) and rules, 'Missing nonempty dictionary')
    require(isinstance(root, str) and root in rules, 'Root must be a defined nonterminal')
    require(not (set(rules) & MACROS), 'A production shadows a fixed macro')
    for name, rhs in rules.items():
        require(isinstance(name, str) and name, 'Invalid nonterminal name')
        require(isinstance(rhs, list) and len(rhs) >= 2, 'A production needs at least two symbols')
        if binary:
            require(len(rhs) == 2, 'Reference productions must be binary')
    active, memo = set(), {}

    def symbol(item):
        if isinstance(item, list):
            require(len(item) == 3 and type(item[2]) is int,
                    'Malformed primitive token')
            token = tuple(item)
            require(token in (INC, BREAK), 'Unexpected primitive token')
            return (token,)
        require(isinstance(item, str), 'Expected a named or primitive symbol')
        if item in rules:
            return visit(item)
        require(item in MACROS, 'Undefined symbol: ' + item)
        if item == 'node60':
            return (INC,) * 2
        if item == 'node61':
            return (INC,) * 4
        return (item,)

    def visit(name):
        require(name not in active, 'Cyclic grammar at ' + name)
        if name in memo:
            return memo[name]
        active.add(name)
        result = tuple(token for item in rules[name] for token in symbol(item))
        active.remove(name)
        memo[name] = result
        return result

    word = visit(root)
    require(set(memo) == set(rules), 'Dictionary contains unreachable productions')
    return word, len(memo), sum(len(rhs) - 1 for rhs in rules.values())


def verify():
    ref_raw, reference = read(HERE / 'reference.grammar.json')
    require(hashlib.sha256(ref_raw).hexdigest() == REFERENCE_SHA256,
            'Reference is not the pinned primary PA194 grammar')
    witness_raw, witness = read(HERE / 'min_grammar_result.json')
    expected, reference_count, _ = expand(reference, 'rules', True)
    actual, witness_count, cost = expand(witness, 'productions', False)
    require(len(expected) == 190, 'Unexpected reference macro-word length')
    require(actual == expected, 'Witness macro word differs from pinned PA194')
    require(cost == 67, 'Summed RHS binary cost is not 67')
    word_bytes = json.dumps(actual, separators=(',', ':'), ensure_ascii=True).encode('ascii')
    return {
        'verified': True,
        'repository_commit': COMMIT,
        'reference_repository_path': 'Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/construction/source/pa194.grammar.json',
        'reference_sha256': REFERENCE_SHA256,
        'witness_sha256': hashlib.sha256(witness_raw).hexdigest(),
        'reference_productions': reference_count,
        'witness_productions': witness_count,
        'acyclic': True,
        'all_productions_reachable': True,
        'exact_macro_word_equal': True,
        'expanded_macro_tokens': len(actual),
        'macro_word_json_sha256': hashlib.sha256(word_bytes).hexdigest(),
        'summed_rhs_binary_cost': cost,
        'solver_objective_or_bound_used': False,
        'optimality_verified': False,
        'lower_bound_established': False,
        'tm_correctness_verified': False,
        'scope': 'A feasible straight-line grammar witness of summed RHS binary cost 67 for the pinned 190-token PA194 macro word. No solver optimality, lower bound, source control-flow, scanner, folding, initialization, or TM correctness claim.'
    }


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
