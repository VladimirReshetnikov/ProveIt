#!/usr/bin/env python3
"""Combine shared binomial residues with one certified Pell cap.

This is a research construction over nonnegative integers.  Input releases are
read-only; every new artifact is written below --output.  The inherited C222,
binomial, and exact-power proofs are retained dependencies, not reproved by
the finite checks in this file.
"""
from pathlib import Path
import argparse, hashlib, json, sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
MOD = ROOT / 'vendor/modular'
CAP = ROOT / 'vendor/cap'
sys.path.insert(0, str(MOD))
import build_modular_factorial as modular
sys.path.insert(0, str(CAP))
import capped_pell as capped

h = modular.h
ONE, TWO = h.ONE, h.TWO

if capped.h is not h:
    raise RuntimeError('The two inputs must share the identical compiler module')


class CombinedBuilder(capped.CappedHybrid, modular.ModularFactorialBuilder):
    radix_variant = 'power'
    merge_factorial = True
    denominator_shift = True
    global_cap = True
    pooled_residue = True
    use_additive_indices = True

    def finalize_power_frame(self):
        if self.shared_frame_finalized:
            return
        if not self.power_indices_ready:
            self.known_exponents = {k for _, k, _, _ in self.pending_powers} | {
                r['n'] for r in self.modular_requests}
            self.index_definitions = {out: key for key, out in self.cache.items()}
            _, A, _ = self._scale()
            self._cap()
            for n, k, m, tag in self.pending_powers:
                X, Y = self._index(k)
                T = self._base(n)
                quotient = self.new(tag + '.quotient')
                self.eq(self.add(X, self.mul(Y, n)),
                        self.sum([self.mul(Y, A), m, self.mul(T, quotient)]),
                        tag + '.power_congruence')
                self.macro_log.append({'macro': 'power', 'output': m,
                    'base': n, 'exponent': k, 'shared_scale': True,
                    'common_index_cap': True})
            q, qb, N = [self.radix_data[n] for n in ('radix', 'root_base', 'modulus')]
            for request in self.modular_requests:
                n, den, label = [request[n] for n in ('n', 'den', 'label')]
                X, Y = self._index(n)
                quotient, remainder, slack = [self.new(label + '.modular_' + s)
                    for s in ('quotient', 'remainder', 'rslack')]
                modulus = self.mul(den, q if request['kind'] == 'exact' else N)
                residue = remainder
                if request['kind'] == 'exact':
                    out = request['output']
                    os = self.new(label + '.modular_oslack')
                    residue = self.add(remainder, self.mul(den, out))
                    self.eq(q, self.sum([out, os, ONE]), label + '.digit_bound')
                self.eq(self.add(X, self.mul(qb, Y)),
                        self.sum([self.mul(A, Y), residue, self.mul(modulus, quotient)]),
                        label + '.modular_digit')
                self.eq(den, self.sum([remainder, slack, ONE]), label + '.remainder_bound')
                request.update({'pair': (X, Y), 'quotient': quotient,
                    'remainder': remainder, 'remainder_slack': slack,
                    'modulus': modulus})
            self.power_indices_ready = True
            cc = self._cap()
            if self.global_cap:
                slack = self.new('index_cap.aggregate_slack')
                self.eq(cc['pair'][1], self.sum([cc['index'], ONE, slack] + [
                    Y for X, Y in self.seed_indices.values()]), 'index_cap.all_indices_bound')
                self.cap_bound_certificate = {'index': cc['index'],
                    'cap_ordinate': cc['pair'][1], 'slack': slack,
                    'ordinates': [Y for X, Y in self.seed_indices.values()],
                    'row_label': 'index_cap.all_indices_bound'}
            if self.pooled_residue:
                quotient = self.new('index_cap.error_square_quotient')
                terms = [(-1, [A, quotient]), (1, [quotient])]
                for k, (X, Y) in self.seed_indices.items():
                    terms.extend([(1, [Y, Y]), (-2, [Y, k]), (1, [k, k])])
                self.row(terms, 'index_cap.squared_index_errors')
                self.cap_residue_certificate = {'base': A, 'quotient': quotient,
                    'seeds': [{'exponent': k, 'pair': pair} for k, pair in self.seed_indices.items()],
                    'row_label': 'index_cap.squared_index_errors'}
        # Modular indices must be in the size frame before applying the cap.
        # The old exact-power frame alone did not bound them.
        atoms = {a for (n, k), m in self.powers.items() for a in (n, k, m)} | {
            r['n'] for r in self.modular_requests}
        W, _, _ = self._scale()
        self.eq(W, self.sum([TWO] + sorted(atoms)), 'shared.frame_definition')
        self.frame_atoms = sorted(atoms)
        self.index_product_finalized = True
        self.shared_frame_finalized = True


def generate(out, syntax='cantor', support_cap=32, sparse=False):
    out = Path(out)
    if out.exists() and any(out.iterdir()):
        raise ValueError('Output directory must be empty')
    class RunBuilder(CombinedBuilder):
        global_cap = not sparse
        pooled_residue = not sparse
    previous = h.HybridBuilder
    h.HybridBuilder = RunBuilder
    try:
        b, src, majorant = modular.dl.construct(syntax=syntax, horizon_minimum=16)
    finally:
        h.HybridBuilder = previous
    equation, expanded, metrics = b.export(hashlib.sha256(src).hexdigest(),
        'capped_modular_unified_factorial_' + syntax, True)
    cap_data = {'cap': b.cap_parameters, 'aggregate': b.cap_bound_certificate,
        'residue': b.cap_residue_certificate, 'semantic_frame_atoms': b.frame_atoms,
        'seed_count': len(b.seed_indices), 'sparse': sparse,
        'theorem': 'one certified cap includes all exact and modular indices'}
    meta = {'powers': [{'base': n, 'exponent': k, 'output': v} for (n, k), v in b.powers.items()],
        'factorials': b.factorial_certificates,
        'binomials': [{'n': n, 'k': k, 'output': v} for (n, k), v in b.binomials.items()],
        'ranges': b.range_requests, 'radix': b.radix_data, 'product': b.product_data,
        'amplification': b.amplification_data, 'scale': b.shared_parameters,
        'lower_A': b.scale_lower, 'cap_certificate': cap_data,
        'discriminant': b.pell_D, 'derivations': b.index_derivations,
        'denominator_derivations': b.denominator_derivations,
        'seeds': [{'exponent': k, 'pair': v} for k, v in b.seed_indices.items()],
        'indices': [{'exponent': k, 'pair': v} for k, v in b.shared_indices.items()],
        'modular_requests': b.modular_requests, 'variables': b.variables,
        'rows': b.rows, 'gates': b.gates, 'local_majorant': majorant,
        'syntax': syntax, 'local_names': modular.dl.LOCAL_NAMES,
        'wire_eliminated_source_sha256': equation['wire_eliminated_source_sha256']}
    for name, obj in [('equation.json', equation), ('expanded_polynomial.json', expanded),
        ('METRICS.json', metrics), ('raw_audit_input.json', meta),
        ('local_majorant.json', majorant), ('cap_certificate.json', cap_data)]:
        h.write(out / 'raw' / name, obj)
    target, certificate, polynomial = h.psd.contract(equation, support_cap=support_cap)
    receipt, independent = h.check.verify(equation, target, certificate)
    if polynomial['terms'] != independent:
        raise ValueError('Independent polynomial expansion mismatch')
    for name, obj in [('equation.json', target), ('expanded_polynomial.json', polynomial),
        ('elimination_certificate.json', certificate), ('VERIFICATION.json', receipt)]:
        h.write(out / 'natural' / name, obj)
    result = {'source': metrics, 'natural': receipt, 'syntax': syntax,
        'support_cap': support_cap, 'sparse': sparse, 'exact_power_calls': len(b.powers),
        'seed_indices': len(b.seed_indices), 'derived_indices': len(b.index_derivations),
        'modular_requests': len(b.modular_requests), 'exact_binomials': len(b.binomials),
        'range_binomials': len(b.range_requests), 'factorials': len(b.factorials),
        'local_degree_bound': majorant['emitted_exponent']}
    h.write(out / 'SUMMARY.json', result)
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--syntax', choices=['cantor', 'xx0', 'xy0'], default='cantor')
    p.add_argument('--support-cap', type=int, default=32)
    p.add_argument('--sparse', action='store_true')
    a = p.parse_args()
    print(json.dumps(generate(a.output, a.syntax, a.support_cap, a.sparse), indent=2))
