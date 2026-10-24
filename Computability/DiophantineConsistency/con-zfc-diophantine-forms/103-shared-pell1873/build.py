#!/usr/bin/env python3
"""Build a literal quartic using one batched Pell certificate.

All output coefficients are explicit integers. No mathematical search,
proof oracle, variable exponent, factorial, or binomial remains in the
emitted equation. See proofs/BATCHED_PELL_THEOREM.md for the semantic proof.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path

import polynomial as sparse
import positive_arithmetic
import signed_backend


def exponent_affine_forms(nodes, exponents):
    """Exact linear forms over nonlinear DAG atoms; never assume equality."""
    memo = {}
    def form(i):
        if i in memo:
            return memo[i]
        n = nodes[i]
        if n[0] == 'c':
            answer = ({}, n[1])
        elif n[0] in ('a', 's'):
            left, lc = form(n[1]); right, rc = form(n[2])
            sign = 1 if n[0] == 'a' else -1
            terms = dict(left)
            for k, v in right.items():
                terms[k] = terms.get(k, 0) + sign * v
            answer = ({k: v for k, v in terms.items() if v}, lc + sign * rc)
        elif n[0] == 'm' and any(nodes[j][0] == 'c' for j in n[1:]):
            const, other = (n[1], n[2]) if nodes[n[1]][0] == 'c' else (n[2], n[1])
            terms, c = form(other); factor = nodes[const][1]
            answer = ({k: factor * v for k, v in terms.items() if factor * v}, factor * c)
        else:
            answer = ({i: 1}, 0)
        memo[i] = answer
        return answer
    return {k: form(k) for k in exponents}


def batched_class(base):
    class Batched(positive_arithmetic.positive_class(base)):
        def __init__(self):
            super().__init__()
            self.pending_powers = []
            self.batch = None

        def var(self, label):
            # A factorial value is always positive; making this explicit
            # permits positivity checks without circular macro reasoning.
            if label.startswith('factorial') and '.output' in label:
                return self.addc(super().var(label + ' minus one'), 1)
            value = super().var(label)
            # These signs follow from the retained division/range rows.
            # They are not assumptions used to license power arguments.
            derived_sign = ((label.startswith('binomial') and '.high.' in label)
                            or label.startswith('coordinate divisibility quotient')
                            or label.startswith('index divisibility quotient'))
            if derived_sign:
                if self.nodes[value][0] != 'v':
                    raise ValueError('Expected an unshifted derived-sign input')
                self.unrestricted.add(self.nodes[value][1])
            return value

        def pow(self, n, k):
            key = (n, k)
            if key in self.power_cache:
                return self.power_cache[key]
            if self.batch is not None:
                raise ValueError('Power call after batch finalization')
            self.calls['power'] += 1
            start = (len(self.vars), len(self.eqs), len(self.nodes))
            tag = 'power' + str(self.calls['power'])
            m = self.addc(self.fresh(tag + '.output_minus_one'), 1)
            self.power_cache[key] = m
            self.pending_powers.append({'base': n, 'exponent': k, 'output': m,
                                        'tag': tag})
            self.ledger.append({'kind': 'deferred_positive_power',
                                'arguments': (n, k), 'result': m,
                                'before': start,
                                'after': (len(self.vars), len(self.eqs), len(self.nodes))})
            return m

        def unconstrained(self, label):
            value = self.fresh(label)
            self.unrestricted.add(self.nodes[value][1])
            return value

        def finalize_powers(self):
            if not self.pending_powers or self.batch is not None:
                raise ValueError('Batch must be finalized exactly once')
            prefix_nodes, prefix_eqs = len(self.nodes), len(self.eqs)
            W = self.sum([p[q] for p in self.pending_powers
                          for q in ('base', 'exponent')])
            gap = self.fresh('batch.global_output_gap')
            A = self.addc(self.add(self.sum([p['output'] for p in self.pending_powers]), gap), 2)
            Z = self.unconstrained('batch.bootstrap_ordinate_quotient')
            self.assertpoly(self.norm(self.addc(W, 1), A, self.mul(W, Z)),
                            'batch.bootstrap_norm')

            # Nearby exponents use exact Pell recurrences, not fresh certificates.
            exponents = list(dict.fromkeys(p['exponent'] for p in self.pending_powers))
            forms = exponent_affine_forms(self.nodes, exponents)
            parents = {}
            for k in exponents:
                terms, const = forms[k]
                candidates = [h for h in exponents if forms[h][0] == terms
                              and 0 <= const - forms[h][1] <= 2]
                parents[k] = min(candidates, key=lambda h: forms[h][1])
            seeds = {}
            tags = {k: 'index' + str(i) for i, k in enumerate(exponents)}
            for k in exponents:
                if parents[k] == k:
                    tag = tags[k]
                    X = self.addc(self.fresh(tag + '.X_minus_one'), 1)
                    Y = self.add(k, self.fresh(tag + '.ordinate_gap'))
                    seeds[k] = {'tag': tag, 'k': k, 'X': X, 'Y': Y,
                                'certificate': 'seed'}
            # This build uses only the independently checked shifts +1,+2.
            # The second-order recurrence saves one product for a second step.
            D = self.sub(self.mul(A, A), self.c(1))
            twiceA = self.mul(self.c(2), A)
            pairs = {(k, 0): (j['X'], j['Y']) for k, j in seeds.items()}
            def shifted(k, shift):
                if (k, shift) in pairs:
                    return pairs[k, shift]
                X0, Y0 = shifted(k, 0)
                if shift == 1:
                    pair = (self.add(self.mul(A, X0), self.mul(D, Y0)),
                            self.add(X0, self.mul(A, Y0)))
                elif shift == 2:
                    X1, Y1 = shifted(k, 1)
                    pair = (self.sub(self.mul(twiceA, X1), X0),
                            self.sub(self.mul(twiceA, Y1), Y0))
                else:
                    raise ValueError('Unproved exponent recurrence shift')
                pairs[k, shift] = pair
                return pair
            indexed = {}
            recurrence_records = []
            for k in exponents:
                parent = parents[k]
                if parent not in seeds:
                    raise ValueError('Non-seed recurrence parent')
                shift = forms[k][1] - forms[parent][1]
                X, Y = shifted(parent, shift)
                if shift == 0:
                    indexed[k] = seeds[parent]
                else:
                    indexed[k] = {'tag': tags[k], 'k': k, 'X': X, 'Y': Y,
                                  'certificate': 'recurrence',
                                  'parent_exponent': parent, 'shift': shift}
                    recurrence_records.append({'exponent': k, 'parent_exponent': parent,
                                               'shift': shift,
                                               'linear_atoms': sorted(forms[k][0].items())})
            P = self.prod([j['Y'] for j in seeds.values()])
            fourP = self.mul(self.c(4), P)
            U = self.addc(self.fresh('batch.U_minus_two'), 2)
            v = self.unconstrained('batch.common_ordinate_quotient')
            V = self.mul(self.mul(fourP, P), v)
            B = self.addc(self.mul(fourP,
                                 self.addc(self.fresh('batch.base_progression'), 1)), 1)
            self.assertpoly(self.norm(A, U, V), 'batch.common_auxiliary_norm')
            self.assertpoly(self.mod(B, A, U, 'batch.base_congruence'),
                            'batch.base_congruence')
            for k, j in seeds.items():
                tag, X, Y = j['tag'], j['X'], j['Y']
                # The signed-index theorem recovers the same positive
                # index from either sign of the auxiliary Pell solution.
                sq = self.unconstrained(tag + '.abscissa_progression')
                rq = self.unconstrained(tag + '.ordinate_progression')
                S = self.add(X, self.mul(U, sq))
                R = self.add(k, self.prod([self.c(4), Y, rq]))
                self.assertpoly(self.norm(A, X, Y), tag + '.main_norm')
                self.assertpoly(self.norm(B, S, R), tag + '.index_norm')
                j.update({'S': S, 'R': R, 'sq': sq, 'rq': rq})
            for call in self.pending_powers:
                n, k, m = call['base'], call['exponent'], call['output']
                j = indexed[k]
                T = self.sub(self.prod([self.c(2), A, n]),
                             self.addc(self.mul(n, n), 1))
                self.assertpoly(self.mod(self.add(j['X'], self.mul(j['Y'], n)),
                                         self.add(self.mul(j['Y'], A), m),
                                         T, call['tag'] + '.residue'),
                                call['tag'] + '.residue')
                call['modulus'] = T
                call['index_tag'] = j['tag']
            self.calls['shared_pell_indices'] = len(seeds)
            self.batch = {'prefix_nodes': prefix_nodes, 'prefix_equalities': prefix_eqs,
                          'W': W, 'A': A, 'Z': Z, 'gap': gap,
                          'P': P, 'U': U, 'V': V, 'v': v, 'B': B,
                          'indices': list(indexed.values()),
                          'seed_indices': list(seeds.values()),
                          'recurrence_records': recurrence_records,
                          'powers': self.pending_powers}

    return Batched


def construct():
    root = Path(__file__).resolve().parent
    path = root / 'source' / 'build_direct.py'
    spec = importlib.util.spec_from_file_location('projected_source', path)
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    c, row, output, binding = source.build_circuit(batched_class(source.Compiler))
    c.finalize_powers()
    return c, row, output, binding


def write_equation(destination, affine_cap=16):
    c, row, output, binding = construct()
    circuit = signed_backend.prune(c)
    rows, polynomial, summary = signed_backend.flatten(circuit, affine_cap)
    summary['distinct_exponents'] = len(c.batch['indices'])
    summary['seed_pell_indices'] = len(c.batch['seed_indices'])
    summary['recurrence_derived_indices'] = len(c.batch['recurrence_records'])
    summary['batched_power_calls'] = len(c.batch['powers'])
    summary['global_pell_bootstraps'] = 1
    summary['global_auxiliary_pell_norms'] = 1
    destination.mkdir(parents=True, exist_ok=True)
    raw = {'format': 'mixed-integer-arithmetic-dag-v1', 'variable_names': c.vars,
           'unrestricted_inputs': sorted(c.unrestricted), 'nodes': c.nodes,
           'equalities': c.eqs, 'source_binding': binding,
           'call_ledger': c.ledger, 'batch': c.batch}
    for name, obj in [('circuit.json', circuit), ('residuals.json', rows),
                      ('polynomial.json', polynomial), ('metrics.json', summary),
                      ('semantic_certificate.json', raw),
                      ('local_row.json', {'variables': row.vars, 'nodes': row.nodes,
                                          'output': output})]:
        sparse.dump(destination / name, obj)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parent / 'equations')
    parser.add_argument('--affine-cap', type=int, default=16)
    args = parser.parse_args()
    print(json.dumps(write_equation(args.output, args.affine_cap), indent=2))


if __name__ == '__main__':
    main()
