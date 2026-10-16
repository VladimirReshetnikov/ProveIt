"""Bounded image-closure templates and a small QBC certificate checker.

The syntax utilities in logic.py are retained from the supplied dossier.
This is research reference code, not a verified implementation or TM compiler.
The checker has no assumption/admit rule. All formula-bearing JSON input is
validated; generated axiom instances use capture-avoiding substitution.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any
from logic import (Formula, E, Hole, Not, Imp, All, Ex, And, Iff, all_many,
                   variables, free_variables, substitute, alpha_key, templates,
                   metrics)


def Or(p: Formula, q: Formula) -> Formula:
    return Imp(Not(p), q)


def inhabited() -> Formula:
    # Double-negation-normalized spelling of exists x exists y (x in y).
    return Not(All(0, All(1, Not(E(0, 1)))))


def bic(matrix: Formula | None = None, *, pure: bool = True,
        closing: bool = True, kernel: str = 'subset') -> Formula:
    """Universal closure of BIC; 0 and 1 are the matrix's input/output slots.

    Other free variables are parameters. The bound seed A is fresh; matrices
    may depend on a separate parameter later instantiated to the chosen seed.
    The optional switches are for ablation tests, not accepted theory axioms.
    """
    matrix = Hole(0, 1) if matrix is None else matrix
    base = 1 + max(variables(matrix) | {0, 1})
    x, b, y, a, c, z = range(base, base + 6)
    def at(u: int, v: int) -> Formula:
        return substitute(substitute(matrix, 0, u), 1, v)
    if kernel == 'subset':
        bound = All(z, Imp(E(z, y), E(z, b)))
    elif kernel == 'membership':
        bound = E(y, b)
    else:
        raise ValueError('unknown kernel')
    premise = All(x, Ex(b, All(y, Imp(at(x, y), bound))))
    active = Or(E(x, a), E(x, c)) if closing else E(x, a)
    closed = All(x, Imp(active, All(y, Imp(at(x, y), E(y, c)))))
    conclusion = And(closed, All(y, Imp(E(y, c), Ex(x, at(x, y))))) if pure else closed
    result = Imp(premise, All(a, Ex(c, conclusion)))
    return all_many(sorted(free_variables(matrix) - {0, 1}), result)


def normalize_double_negation(f: Formula) -> Formula:
    if f.op in ('E', '=', 'phi'):
        return f
    if f.op == 'all':
        return All(f.args[0], normalize_double_negation(f.args[1]))
    args = tuple(normalize_double_negation(g) for g in f.args)
    if f.op == 'not' and args[0].op == 'not':
        return args[0].args[0]
    return Formula(f.op, args)


def to_data(f: Formula) -> list:
    if f.op in ('E', '=', 'phi'):
        return [f.op, *f.args]
    if f.op == 'all':
        return ['all', f.args[0], to_data(f.args[1])]
    return [f.op, *(to_data(g) for g in f.args)]


def nat(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError('expected a nonnegative integer, not a boolean')
    return x


def from_data(x: Any) -> Formula:
    """Strict parser for the equality-free, hole-free executing language."""
    if not isinstance(x, list) or not x or not isinstance(x[0], str):
        raise ValueError('formula must be a tagged JSON array')
    tag = x[0]
    if tag == 'E' and len(x) == 3:
        return E(nat(x[1]), nat(x[2]))
    if tag == 'not' and len(x) == 2:
        return Not(from_data(x[1]))
    if tag == 'imp' and len(x) == 3:
        return Imp(from_data(x[1]), from_data(x[2]))
    if tag == 'all' and len(x) == 3:
        return All(nat(x[1]), from_data(x[2]))
    raise ValueError('unsupported formula tag, arity, equality, or matrix hole')


def bottom() -> Formula:
    # A closed, logically refutable target, without a falsity constructor.
    p = E(0, 0)
    return Not(All(0, Imp(p, p)))


def check(records: Any) -> list[Formula]:
    """Execute an assumption-free Hilbert certificate; raise on any bad record.

    Logical axiom rules: L1, L2, L3, Q1, Q2. Inference rules: MP, GEN.
    Theory rules: N, CG, BIC. ALPHA admits only alpha-equivalent renamings.
    Indices are zero-based and must refer strictly to earlier records.
    """
    if not isinstance(records, list) or not records:
        raise ValueError('expected a nonempty certificate array')
    out: list[Formula] = []
    def previous(index: Any) -> Formula:
        i = nat(index)
        if i >= len(out):
            raise ValueError('proof reference is not an earlier line')
        return out[i]
    for number, rec in enumerate(records):
        try:
            if not isinstance(rec, list) or not rec or not isinstance(rec[0], str):
                raise ValueError('proof record must be a tagged array')
            rule, data = rec[0], rec[1:]
            if rule == 'L1' and len(data) == 2:
                a, b = map(from_data, data)
                f = Imp(a, Imp(b, a))
            elif rule == 'L2' and len(data) == 3:
                a, b, c = map(from_data, data)
                f = Imp(Imp(a, Imp(b, c)), Imp(Imp(a, b), Imp(a, c)))
            elif rule == 'L3' and len(data) == 2:
                a, b = map(from_data, data)
                f = Imp(Imp(Not(a), Not(b)), Imp(b, a))
            elif rule == 'Q1' and len(data) == 3:
                x, y, a = nat(data[0]), nat(data[1]), from_data(data[2])
                f = Imp(All(x, a), substitute(a, x, y))
            elif rule == 'Q2' and len(data) == 3:
                x, a, b = nat(data[0]), from_data(data[1]), from_data(data[2])
                if x in free_variables(a):
                    raise ValueError('Q2 variable is free in antecedent')
                f = Imp(All(x, Imp(a, b)), Imp(a, All(x, b)))
            elif rule == 'MP' and len(data) == 2:
                a, implication = previous(data[0]), previous(data[1])
                if implication.op != 'imp' or alpha_key(implication.args[0]) != alpha_key(a):
                    raise ValueError('modus ponens mismatch')
                f = implication.args[1]
            elif rule == 'GEN' and len(data) == 2:
                f = All(nat(data[0]), previous(data[1]))
            elif rule == 'ALPHA' and len(data) == 2:
                old, f = previous(data[0]), from_data(data[1])
                if alpha_key(old) != alpha_key(f):
                    raise ValueError('not alpha-equivalent')
            elif rule == 'N' and not data:
                f = inhabited()
            elif rule == 'CG' and not data:
                f = templates()['CG']
            elif rule == 'BIC' and len(data) == 1:
                f = bic(from_data(data[0]))
            else:
                raise ValueError('unknown rule or incorrect arity')
            out.append(f)
        except (ValueError, TypeError, KeyError) as e:
            raise ValueError(f'line {number}: {e}') from e
    return out


def identity_certificate(a: Formula) -> list:
    aa = Imp(a, a)
    return [['L1', to_data(a), to_data(aa)], ['L1', to_data(a), to_data(a)],
            ['L2', to_data(a), to_data(aa), to_data(a)], ['MP', 0, 2], ['MP', 1, 3]]


def write_metrics(root: Path) -> dict:
    ts = templates()
    ts.update({'N': inhabited(), 'BIC': bic()})
    variants = {'RCC': ['CP', 'GIC'], 'QCC': ['CG', 'CP', 'GIC'],
                'EBC': ['Ext', 'N', 'BIC'], 'QBC': ['CG', 'N', 'BIC'],
                'RBC0_uncalibrated': ['N', 'BIC']}
    result = {'basis': 'E, equality (reference only), phi (template only), not, imp, all',
              'exclusions': 'Variable encoding, schema parameters, logical axioms, proof engine, initializer, target and TM backend are not charged.',
              'templates': {k: {'expanded': metrics(f),
                  'double_negation_normalized': metrics(normalize_double_negation(f))}
                  for k, f in ts.items()},
              'totals': {k: {mode: sum(metrics(fn(ts[t]))['tree_nodes'] for t in names)
                  for mode, fn in [('expanded', lambda x: x),
                                   ('double_negation_normalized', normalize_double_negation)]}
                  for k, names in variants.items()}}
    for directory in ['results', 'examples']:
        (root / directory).mkdir(parents=True, exist_ok=True)
    rows = []
    for key in ['Ext', 'CG', 'N', 'BIC', 'CP', 'GIC']:
        a = result['templates'][key]['expanded']['tree_nodes']
        b = result['templates'][key]['double_negation_normalized']['tree_nodes']
        rows.append(r'$\mathsf{' + key + '}$ & ' + str(a) + ' & ' + str(b) + r'\\')
    (root / 'results' / 'template_rows.tex').write_text('\n'.join(rows) + '\n', encoding='utf-8')
    (root / 'results' / 'metrics.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    (root / 'examples' / 'bic_template.json').write_text(json.dumps(to_data(bic()), indent=2) + '\n')
    cert = identity_certificate(E(0, 0)) + [['GEN', 0, 4]]
    (root / 'examples' / 'identity.json').write_text(json.dumps(cert, indent=2) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path)
    parser.add_argument('--metrics', action='store_true')
    args = parser.parse_args()
    if args.metrics:
        result = write_metrics(Path(__file__).resolve().parents[1])
        print(json.dumps(result['totals'], indent=2))
    elif args.certificate:
        try:
            final = check(json.loads(args.certificate.read_text()))[-1]
        except (ValueError, OSError, RecursionError) as error:
            parser.exit(1, f'Rejected: {error}\n')
        print(json.dumps({'valid_certificate': True,
                          'is_refutation': alpha_key(final) == alpha_key(bottom()),
                          'final_formula': to_data(final)}, indent=2))
    else:
        parser.error('supply a certificate path or --metrics')
