#!/usr/bin/env python3
"""Use one binomial for factorial recovery and reciprocal CRT product.

The square-output factorial identity is inherited. The identification with the
reciprocal product, and the consequent pure amplified radix, are this variant.
Only explicit output directories are written. The reviewed round14 engine is
imported read-only; every exponent is compiled by its ordinary Pell graph.
"""
from pathlib import Path
import argparse
import json
import sys

# Preserve the imported release even when this module is imported by a caller
# that omitted PYTHONDONTWRITEBYTECODE from its environment.
sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24'
sys.path.insert(0, str(BASE / 'architecture'))
import build_derived_label_range as derived
import build_factorial_carrier as slack

h = derived.h
ONE = h.ONE
const = h.const
OldBuilder = h.HybridBuilder


class UnifiedProductBuilder(OldBuilder):
    squared_radix_base = False
    def factorial(self, n):
        if n in self.factorials:
            return self.factorials[n]
        if self.factorials:
            raise ValueError('This architecture is proved for exactly one factorial')
        tag = 'fact0'
        out = self.new(tag + '.output')
        self.factorials[n] = out
        rho = self.square(out)
        self.shared_factorial_radius = rho
        c = self.binomial(self.add(rho, n), n)
        numerator = self.power(self.add(rho, ONE), n)
        remainder = self.new(tag + '.remainder')
        complement = self.new(tag + '.slack')
        self.eq(self.add(numerator, c),
                self.sum([self.mul(c, out), remainder, ONE]), tag + '.ceiling')
        self.eq(c, self.sum([remainder, complement, ONE]), tag + '.remainder_bound')
        self.macro_log.append({'macro': 'factorial', 'output': out, 'n': n,
                               'square_output_radius': True,
                               'shared_reciprocal_product': True})
        self.factorial_certificates.append({'input': n, 'output': out,
            'radius': rho, 'binomial': c, 'numerator': numerator,
            'remainder': remainder, 'slack': complement,
            'selfbounding': True, 'square_output_radius': True})
        self.factorial_radix = {'H': n, 'rho': rho, 'numerator': numerator,
                               'factorial': out}
        return out

    def finalize_binomials(self):
        if getattr(self, 'binomials_finalized', False):
            raise ValueError('Repeated binomial finalization')
        self.binomials_finalized = True
        if len(self.binomials) != 1:
            raise ValueError('Factorial and reciprocal product were not identified')
        if self.factorial_certificates[0]['binomial'] != self.product_data['product']:
            raise ValueError('Factorial/product output mismatch')
        moduli = {item[2] for item in self.range_requests}
        if len(moduli) != 1:
            raise ValueError('One common amplified modulus required')
        N = next(iter(moduli))
        K = self.amplification_data['K']
        aggregate_requests = getattr(self, 'aggregate_requests', self.range_requests)
        count = len(aggregate_requests)
        aggregate = self.new('crt.aggregate_representative_slack')
        self.eq(self.mul(const(count), self.square(N)),
                self.add(self.sum(n for n, _, _, _ in aggregate_requests), aggregate),
                'crt.aggregate_representative_bound')
        q = self.power(self.square(N) if self.squared_radix_base else N, K)
        for i, ((n, k), out) in enumerate(self.binomials.items()):
            tag = 'choose' + str(i)
            numerator = self.power(self.add(q, ONE), n)
            den = self.power(q, k)
            high, rem, remslack, outslack = [self.new(tag + '.' + role)
                for role in ('high', 'remainder', 'rslack', 'oslack')]
            self.eq(numerator,
                self.add(self.mul(den, self.add(self.mul(q, high), out)), rem),
                tag + '.digit')
            self.eq(den, self.sum([rem, remslack, ONE]), tag + '.remainder_bound')
            self.eq(q, self.sum([out, outslack, ONE]), tag + '.digit_bound')
        for i, (n, k, modulus, label) in enumerate(self.range_requests):
            numerator = self.power(self.add(q, ONE), n)
            den = self.power(q, k)
            high, rem, remslack = [self.new('range' + str(i) + '.' + role)
                for role in ('quotient', 'remainder', 'slack')]
            self.eq(numerator, self.add(self.product([den, modulus, high]), rem),
                    label + '.quotient_multiple')
            self.eq(den, self.sum([rem, remslack, ONE]), label + '.remainder_bound')
        self.radix_data = {'radix': q, 'modulus': N, 'K': K,
            'V': self.factorial_radix['numerator'], 'aggregate_count': count,
            'aggregate_slack': aggregate,
            'kind': '(N^2)^K' if self.squared_radix_base else 'N^K',
            'bound': 'count*N^2',
            'bootstrap': 'V<=B*F<B^2<N^K before interpreting B',
            'exact_binomials': len(self.binomials),
            'range_binomials': len(self.range_requests)}
        self.amplification_data['unified_factorial_product'] = True


def construct(syntax='cantor', horizon_minimum=16, labels='derived', squared_radix_base=False):
    if horizon_minimum < 16:
        raise ValueError('The uniform padded-horizon proof requires t>=16')
    h.HybridBuilder = UnifiedProductBuilder
    UnifiedProductBuilder.squared_radix_base = squared_radix_base
    try:
        return (derived if labels == 'derived' else slack).construct(syntax, horizon_minimum)
    finally:
        h.HybridBuilder = OldBuilder


def generate(out, syntax='cantor', horizon_minimum=16, labels='derived', squared_radix_base=False):
    if horizon_minimum < 16:
        raise ValueError('The uniform padded-horizon proof requires t>=16')
    h.HybridBuilder = UnifiedProductBuilder
    UnifiedProductBuilder.squared_radix_base = squared_radix_base
    try:
        result = (derived if labels == 'derived' else slack).generate(out, syntax, horizon_minimum)
    finally:
        h.HybridBuilder = OldBuilder
    result.update({'unified_factorial_product': True, 'pure_amplified_radix': True,
                   'label_bound_mode': labels, 'squared_radix_base': squared_radix_base})
    h.write(Path(out) / 'SUMMARY.json', result)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--syntax', choices=['cantor', 'xx0', 'xy0'], default='cantor')
    parser.add_argument('--labels', choices=['derived', 'slack'], default='derived')
    parser.add_argument('--horizon-minimum', type=int, default=16)
    parser.add_argument('--squared-radix-base', action='store_true')
    args = parser.parse_args()
    if args.horizon_minimum < 16:
        raise ValueError('The uniform padded-horizon proof requires t>=16')
    print(json.dumps(generate(args.output, args.syntax, args.horizon_minimum,
                              args.labels, args.squared_radix_base), indent=2))
