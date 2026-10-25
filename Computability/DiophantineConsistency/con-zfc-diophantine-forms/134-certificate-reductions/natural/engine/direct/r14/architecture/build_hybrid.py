#!/usr/bin/env python3
"""Reciprocal-prime-power CRT, with a small self-bounding factorial.

Imports the inspected frozen shell/reciprocal release read-only. All generated
files go to the explicit --output directory. No repository writes or uploads.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
SHELL = ROUND / 'intake/shell/shell'
sys.path.insert(0, str(SHELL / 'code'))
from shared_radius import SharedRadiusBuilder
from norm_transform import ROOT
import build_projected as bp
from build_equation import ONE, TWO, const
import shell_source
CANTOR_SOURCE = bp.ng.direct_source

def imported(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

psd = imported('hybrid_psd_contract', ROOT / 'code/psd_contract/contract.py')
check = imported('hybrid_psd_check', ROOT / 'code/psd_contract/check.py')

def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n')

class HybridBuilder(SharedRadiusBuilder):
    def moduli_product(self, t, F):
        T = self.square(F)
        B = self.binomial(self.add(T, t), t)
        self.product_data = {'horizon': t, 'factorial': F, 'square': T, 'product': B}
        return B

    def finalize_binomials(self):
        if getattr(self, 'binomials_finalized', False):
            raise ValueError('repeated binomial finalization')
        self.binomials_finalized = True
        moduli = {item[2] for item in self.range_requests}
        if len(moduli) != 1:
            raise ValueError('one common amplified modulus required')
        N = next(iter(moduli))
        K = self.amplification_data['K']
        aggregate_requests = getattr(self, 'aggregate_requests', self.range_requests)
        count = len(aggregate_requests)
        aggregate = self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(const(count), self.square(N)),
                self.add(self.sum(n for n, _, _, _ in aggregate_requests), aggregate),
                'crt.aggregate_representative_bound')
        V = self.factorial_radix['numerator']
        q = self.mul(N, self.power(self.sum([N, V, ONE]), K))
        for i, ((n, k), out) in enumerate(self.binomials.items()):
            tag = 'choose' + str(i)
            numerator = self.power(self.add(q, ONE), n)
            den = self.power(q, k)
            h, r, rs, os = [self.new(tag + '.' + s) for s in ('high', 'remainder', 'rslack', 'oslack')]
            self.eq(numerator, self.add(self.mul(den, self.add(self.mul(q, h), out)), r), tag + '.digit')
            self.eq(den, self.sum([r, rs, ONE]), tag + '.remainder_bound')
            self.eq(q, self.sum([out, os, ONE]), tag + '.digit_bound')
        for i, (n, k, modulus, label) in enumerate(self.range_requests):
            numerator = self.power(self.add(q, ONE), n)
            den = self.power(q, k)
            h, r, s = [self.new('range' + str(i) + '.' + role) for role in ('quotient', 'remainder', 'slack')]
            self.eq(numerator, self.add(self.product([den, modulus, h]), r), label + '.quotient_multiple')
            self.eq(den, self.sum([r, s, ONE]), label + '.remainder_bound')
        self.radix_data = {'radix': q, 'modulus': N, 'K': K, 'V': V,
                           'aggregate_count': count, 'aggregate_slack': aggregate,
                           'kind': 'N*(N+V+1)^K', 'bound': 'count*N^2',
                           'exact_binomials': len(self.binomials), 'range_binomials': len(self.range_requests)}

def construct(syntax='cantor'):
    bp.ng.direct_source = CANTOR_SOURCE
    if syntax != 'cantor':
        shell_source.SHELL_SCHEME = syntax
        bp.ng.direct_source = shell_source.direct_source
    b = HybridBuilder(positive_powers=True)
    sourcebytes = (bp.ng.UP / 'provenance/upstream/wire_eliminated_source.json').read_bytes()
    source = json.loads(sourcebytes)
    params = {n: b.new(n + ('0' if n == 't' else ''), 'outer') for n in ('t', 'x', 'y', 'M0')}
    params['t'] = b.add(params['t'], ONE)
    t, x, y, M0 = [params[n] for n in ('t', 'x', 'y', 'M0')]
    labelcert = bp.label_majorant(source)
    basepower = b.power(b.add(t, ONE), t)
    carrier = bp.ng.syn.fixed_power(b, basepower, labelcert['carrier_exponent'])
    b.eq(carrier, b.add(M0, ONE), 'projected.carrier')
    u0, r0, ut = [b.new('endpoint.' + n) for n in ('u0', 'r0', 'ut')]
    dt = b.add(b.mul(b.add(t, ONE), y), ONE)
    b.eq(x, b.add(b.add(M0, TWO), b.mul(b.add(y, ONE), u0)), 'endpoint.first_quotient')
    b.eq(y, b.sum([M0, r0, TWO]), 'endpoint.first_remainder')
    b.eq(x, b.add(ONE, b.mul(dt, ut)), 'endpoint.last_quotient')
    bounds = {n: t if i < 4 else y if i < 6 else x for i, n in enumerate(bp.LOCAL_NAMES)}
    encoded = {n: b.add(b.new('crt.encoded.' + n), ONE) for n in bp.LOCAL_NAMES}
    C = b.add(b.new('crt.encoded_index_minus_one'), ONE)
    boundcert = bp.local_majorant(source)
    R = b.sum([TWO, t, x, y, M0])
    # The already required carrier forces R >= 2^L. The elementary
    # carrier-budget lemma then gives R^E < 2^R. No huge coefficient E
    # belongs in the equation. K=2R also supplies the sharper radix bound.
    L, E = labelcert['carrier_exponent'], boundcert['emitted_exponent']
    if L < 8 or E > 2 * L:
        raise ValueError('carrier-budget lemma hypotheses require reproof')
    K = b.mul(TWO, R)
    F = b.factorial(t)
    B = b.moduli_product(t, F)
    T = b.product_data['square']
    N = b.power(B, K)
    b.amplification_data = {'B': B, 'K': K, 'N': N, 'F': F, 't': t, 'R': R,
                           'local_degree_bound': E, 'carrier_exponent': L,
                           'budget': '2R', 'carrier_budget_lemma': 'L>=8,E<=2L',
                           'index': C, 'index_precision': 'K', 'completeness_precision': '2K'}
    for n in bp.LOCAL_NAMES:
        b.divisible_binomial(encoded[n], b.add(bounds[n], ONE), N, 'crt.range.' + n)
    b.divisible_binomial(C, t, N, 'crt.range.index')
    iq = b.new('crt.index_quotient')
    b.eq(b.sum([C, T, ONE]), b.mul(B, iq), 'crt.reciprocal_index_congruence')
    value = bp.projected_source(b, source, params | encoded, C)
    quotient = b.new('crt.nonnegative_quotient')
    b.eq(value, b.mul(N, quotient), 'crt.nonnegative_evaluation')
    b.finalize_binomials()
    b.finalize_power_frame()
    return b, sourcebytes, labelcert, boundcert

def generate(out, syntax='cantor'):
    out = Path(out)
    b, src, lc, bc = construct(syntax)
    eq, poly, metrics = b.export(hashlib.sha256(src).hexdigest(), 'reciprocal_prime_power_' + syntax, True)
    meta = {'powers': [{'base': n, 'exponent': k, 'output': v} for (n, k), v in b.powers.items()],
            'factorials': b.factorial_certificates,
            'binomials': [{'n': n, 'k': k, 'output': v} for (n, k), v in b.binomials.items()],
            'ranges': b.range_requests, 'radix': b.radix_data, 'product': b.product_data,
            'amplification': b.amplification_data,
            'scale': b.shared_parameters, 'auxiliary': b.common_index_parameters,
            'discriminant': b.pell_D, 'derivations': b.index_derivations,
            'seeds': [{'exponent': k, 'pair': v} for k, v in b.seed_indices.items()],
            'indices': [{'exponent': k, 'pair': v} for k, v in b.shared_indices.items()],
            'variables': b.variables, 'rows': b.rows, 'gates': b.gates,
            'local_majorant': bc, 'label_majorant': lc, 'syntax': syntax}
    for filename, obj in [('equation.json', eq), ('expanded_polynomial.json', poly),
                          ('METRICS.json', metrics), ('raw_audit_input.json', meta),
                          ('label_majorant.json', lc), ('local_majorant.json', bc)]:
        write(out / 'raw' / filename, obj)
    target, cert, expanded = psd.contract(eq, support_cap=64)
    receipt, independent = check.verify(eq, target, cert)
    if expanded['terms'] != independent:
        raise ValueError('independent expanded polynomial mismatch')
    for filename, obj in [('equation.json', target), ('elimination_certificate.json', cert),
                          ('expanded_polynomial.json', expanded), ('VERIFICATION.json', receipt)]:
        write(out / 'natural' / filename, obj)
    counts = {'source': metrics, 'natural': receipt, 'syntax': syntax,
              'power_calls': len(b.powers), 'seed_indices': len(b.seed_indices),
              'derived_indices': len(b.index_derivations), 'exact_binomials': len(b.binomials),
              'range_binomials': len(b.range_requests), 'factorials': len(b.factorials)}
    write(out / 'SUMMARY.json', counts)
    return counts

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--syntax', choices=['cantor', 'xx0', 'xy0'], default='cantor')
    args = parser.parse_args()
    print(json.dumps(generate(args.output, args.syntax), indent=2))
