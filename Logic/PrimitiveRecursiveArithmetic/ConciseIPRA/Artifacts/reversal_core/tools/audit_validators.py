"""Finite corroboration of the simultaneous structural-induction proof."""
import ast
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]


def functions(name, selected):
    tree = ast.parse((ROOT / ('controls' if name.startswith('control_') else 'code') / name).read_text())
    definitions = [node for node in tree.body
                   if isinstance(node, ast.FunctionDef) and node.name in selected]
    namespace = {}
    exec(compile(ast.Module(body=definitions, type_ignores=[]), name, 'exec'), namespace)
    return namespace


def main():
    old = functions('control_old_strict_eqd.py', {'term', 'formula'})
    new = functions('checker_rev_strict_eqd.py', {'v'})
    full_old = functions('control_old_strict_full.py', {'term', 'formula'})
    full_new = functions('checker_rev_strict_full.py', {'v'})
    rng = random.Random(20261111)
    leaves = [None, False, True, -100, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8,
              100, 0.0, 1.0, -0.5, 'x', {}, float('inf'), float('-inf'), float('nan')]

    def arbitrary(depth):
        if depth == 0 or rng.random() < 0.45:
            return rng.choice(leaves)
        return [arbitrary(depth - 1) for _ in range(rng.randrange(6))]

    def term(depth, slots):
        if depth == 0 or rng.random() < 0.5:
            return rng.choice([0] + list(range(3, 3 + 2 * slots, 2)))
        arity = rng.choice([1, 3])
        return [term(depth - 1, slots + (5 - arity) // 2) for _ in range(arity)]

    def formula(depth, slots, full):
        choices = [1, 2, 3] if full and depth else [1, 2] if depth else [2]
        arity = rng.choice(choices)
        if arity == 2:
            return [term(3, slots) for _ in range(2)]
        body = formula(depth - 1, slots + (5 - arity) // 2, full)
        return [body] * arity

    cases = leaves + [[]] + [arbitrary(4) for _ in range(10000)]
    cases += [formula(3, 0, full) for full in (False, True) for _ in range(1500)]
    comparisons = accepted_eqd = accepted_full = 0
    for value in cases:
        for slots in range(5):
            eqd_a = bool(old['formula'](value, slots))
            eqd_b = bool(new['v'](value, 2 * slots))
            full_a = bool(full_old['formula'](value, slots))
            full_b = bool(full_new['v'](value, 2 * slots))
            if (eqd_a, full_a) != (eqd_b, full_b):
                raise AssertionError(('formula', value, slots))
            for validate in (new['v'], full_new['v']):
                if bool(old['term'](value, slots)) != bool(validate(value, 3 + 2 * slots)):
                    raise AssertionError(('term', value, slots))
            comparisons += 4
            accepted_eqd += int(eqd_a)
            accepted_full += int(full_a)
    result = {
        'seed': 20261111, 'comparisons': comparisons, 'mismatches': 0,
        'eqd_accepted_cases': accepted_eqd, 'full_native_accepted_cases': accepted_full,
        'scope_slots': list(range(5)),
        'scope': 'Term and formula modes; generated canonical trees and malformed JSON values',
        'limitation': 'Finite corroboration; universal parser equivalence follows by structural induction',
    }
    (ROOT / 'evidence/parser_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
