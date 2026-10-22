#!/usr/bin/env python3
"""Untrusted discovery aid: search a fixed pool of existing schemas for S.

The resulting expression is checked separately by Lean and Rocq. A failed
search here is not a lower bound on possible proofs or on other schema pools.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import re


def parse(source):
    tokens = re.findall(r'wim|L\.imp|[a-zA-Z_][a-zA-Z_0-9]*|[()]', source)
    i = 0

    def term():
        nonlocal i
        token = tokens[i]
        i += 1
        if token == '(':
            value = term()
            assert tokens[i] == ')'
            i += 1
            return value
        if token in ('wim', 'L.imp'):
            return (term(), term())
        return token

    value = term()
    assert i == len(tokens), (tokens, i)
    return value


def resolve(term, env):
    while isinstance(term, str) and term in env:
        term = env[term]
    return term


def occurs(variable, term, env):
    term = resolve(term, env)
    return term == variable if isinstance(term, str) else any(
        occurs(variable, child, env) for child in term)


def unify(left, right, env):
    left, right = resolve(left, env), resolve(right, env)
    if left == right:
        return True
    if isinstance(left, str) and not left.startswith('$'):
        if occurs(left, right, env):
            return False
        env[left] = right
        return True
    if isinstance(right, str) and not right.startswith('$'):
        return unify(right, left, env)
    if isinstance(left, tuple) and isinstance(right, tuple):
        return unify(left[0], right[0], env) and unify(left[1], right[1], env)
    return False


def instantiate(term, env):
    term = resolve(term, env)
    return tuple(instantiate(child, env) for child in term) if isinstance(term, tuple) else term


def rename(term, prefix):
    return tuple(rename(child, prefix) for child in term) if isinstance(term, tuple) else prefix + term


def shape(term):
    variables = {}

    def visit(value):
        if isinstance(value, tuple):
            return tuple(visit(child) for child in value)
        if value not in variables:
            variables[value] = f'v{len(variables)}'
        return variables[value]

    return visit(term)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--core', type=Path, default=Path(__file__).resolve().parents[1] /
                        'lean_basis/BusyBeaver/ZFC/DominatedImplication.lean')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    source = args.core.read_bytes()
    schemas = []
    for match in re.finditer(r'private theorem (d\d+)\b(.*?) :=', source.decode(), re.S):
        name, header = match.groups()
        # The inherited guarded schemas have an explicit hb hypothesis.
        if 'hb' not in header:
            schemas.append((name, parse(re.split(r':\s*T\s+', header)[-1])))
    goal = (('$a', ('$b', '$c')), (('$a', '$b'), ('$a', '$c')))
    one_hits, derived = [], []
    for (name1, schema1), (name2, schema2) in itertools.product(schemas, repeat=2):
        left, right, env = rename(schema1, 'L'), rename(schema2, 'R'), {}
        if isinstance(left, tuple) and unify(left[0], right, env):
            derived.append((instantiate(left[1], env), (name1, name2, dict(env))))
            trial = dict(env)
            if unify(left[1], goal, trial):
                one_hits.append((1, name1, name2, trial))
    distinct = {}
    for term, proof in derived:
        distinct.setdefault(shape(term), (term, proof))
    two_hit = None
    for (term, proof), (name, schema) in itertools.product(distinct.values(), schemas):
        for direction in (0, 1):
            a, b = rename(term, 'D'), rename(schema, 'S')
            left, right = (a, b) if direction == 0 else (b, a)
            env = {}
            if isinstance(left, tuple) and unify(left[1], goal, env) and unify(left[0], right, env):
                two_hit = (2, direction, proof, name, env)
                break
        if two_hit is not None:
            break
    result = {
        'scope': 'Untrusted bounded discovery in the extracted unconditional schema pool; no minimality claim.',
        'core_sha256': hashlib.sha256(source).hexdigest(),
        'schema_names': [name for name, _ in schemas],
        'one_mp_instances': len(derived),
        'distinct_one_mp_shapes': len(distinct),
        'one_mp_hits_in_this_pool': one_hits,
        'first_two_mp_hit': two_hit,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in
                      ('one_mp_instances', 'distinct_one_mp_shapes')}, indent=2))
    print('Found a two-MP candidate:', two_hit is not None)


if __name__ == '__main__':
    main()
