#!/usr/bin/env python3
"""Read-only static/finite audit; prints JSON, never invokes Lean or writes files.

Run: python3 verify_power.py [--upstream PATH]
The optional upstream is only read to confirm each source snapshot byte-for-byte.
This is not Lean elaboration/kernel validation and not a proof by enumeration.
"""
from pathlib import Path
import argparse
import difflib
import functools
import hashlib
import json
import math
import re


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def declarations(text):
    """Sufficient for these flat theorem-only files, not a general Lean parser."""
    out = {}
    pattern = re.compile(r"(?m)^(?P<private>private )?theorem (?P<name>\w+)[\s\S]*? :=")
    for match in pattern.finditer(text):
        if not match.group('private'):
            out[match.group('name')] = match.group(0)
    return out


@functools.lru_cache(None)
def finite_order(m, x):
    """Exact order of a residue, using 0 for no positive return to one.

    ZMod 0 is Z, not a fictitious finite residue class. Inputs here are nonnegative.
    """
    if m == 0:
        return 1 if x == 1 else 0
    x %= m
    y, one = 1 % m, 1 % m
    # A first positive return in a finite monoid has length at most its cardinality.
    for k in range(1, m + 1):
        y = y * x % m
        if y == one:
            return k
    return 0


def residue_power(x, k, m):
    return pow(x, k, m) if m else pow(x, k)


def divides(m, n):
    return n == 0 if m == 0 else n % m == 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--upstream', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'manifest.json').read_text())
    rows = []
    total = [0, 0]
    allowed_changes = {
        'PrimePowerOrder.lean': {'pow_cast_eq_one_iff'},
        'CurrentPowerCoordinates2011.lean': {
            'order_product', 'generator_cast_auxiliary', 'generator_cast_C0', 'block_order'
        },
    }
    for row in manifest['patches']:
        before_bytes = (root / row['source']).read_bytes()
        after_bytes = (root / row['proposed']).read_bytes()
        require(digest(before_bytes) == row['before_sha256'], 'source hash mismatch')
        require(digest(after_bytes) == row['after_sha256'], 'candidate hash mismatch')
        if args.upstream:
            require((args.upstream / row['file']).read_bytes() == before_bytes,
                    'upstream/source snapshot mismatch')
        before, after = before_bytes.decode(), after_bytes.decode()
        expected_patch = ''.join(difflib.unified_diff(
            before.splitlines(True), after.splitlines(True),
            fromfile='a/' + row['file'], tofile='b/' + row['file']))
        require((root / row['path']).read_text() == expected_patch,
                'patch is not exact whole-file unified diff')
        require(declarations(before) == declarations(after), 'public theorem signature change')
        # Remove the targeted theorem bodies, then require every remaining byte unchanged.
        def erase_targets(text):
            name = Path(row['file']).name
            for target in allowed_changes[name]:
                pat = re.compile(r'(?m)^(theorem ' + re.escape(target) +
                                 r'[\s\S]*? :=)[\s\S]*?(?=\n\n|\Z)')
                require(len(pat.findall(text)) == 1, 'ambiguous targeted theorem span')
                text = pat.sub(lambda m: m.group(1) + ' <PROOF>', text)
            if name == 'CurrentPowerCoordinates2011.lean':
                removed = ('/-- Explicit modulus transport avoids any evaluation of the huge base. -/\n'
                           'private theorem order_transport (x k m n : ℕ) (h : m = n) :\n'
                           '    orderOf ((x : ZMod m)^k) = orderOf ((x : ZMod n)^k) := by\n'
                           '  subst n\n  rfl\n\n')
                text = text.replace(removed, '')
            return text
        require(erase_targets(before) == erase_targets(after), 'non-targeted source byte changed')
        require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac)\b', after),
                'unexpected proof escape or evaluator')
        physical = len(before.splitlines()) - len(after.splitlines())
        nonblank = sum(bool(l.strip()) for l in before.splitlines()) - sum(bool(l.strip()) for l in after.splitlines())
        require(physical == row['before_physical'] - row['after_physical'], 'physical count mismatch')
        require(nonblank == row['before_nonblank'] - row['after_nonblank'], 'nonblank count mismatch')
        total[0] += physical
        total[1] += nonblank
        rows.append({'patch': row['name'], 'public_signatures_identical': True,
                     'non_target_bytes_identical': True, 'net_physical_removed': physical,
                     'net_nonblank_removed': nonblank})

    prime = (root / 'proposed/PrimePowerOrder.lean').read_text()
    current = (root / 'proposed/CurrentPowerCoordinates2011.lean').read_text()
    require('(hg : 1 ≤ g)' in prime and 'Nat.cast_sub (one_le_pow₀ hg)' in prime,
            'natural subtraction guard lost')
    require('attribute [local irreducible] CurrentControllerData2011.B' in current,
            'huge base irreducibility lost')
    require('private theorem order_transport' not in current and 'order_transport' not in current,
            'private transport was not fully removed')
    require('simpa only [modulus_factorization] using full_order k' in current,
            'unexpected transport implementation')
    require('using generator_order_succ 0' in current and 'using full_order 0' in current,
            'zero-exponent specializations not retained')
    # The coordinate witnesses, finite-bijection construction, actual generator
    # certificates and all their guards remain completely outside the patch.
    for name in ('ControllerPowerCoordinates', 'CurrentAuxiliaryOrder2011'):
        require(not (root / 'proposed' / (name + '.lean')).exists(),
                'unchanged reference has an unexpected candidate')

    cast_cases = 0
    for m in range(65):
        for g in range(1, 34):
            for k in range(13):
                lhs = residue_power(g, k, m) == (1 % m if m else 1)
                rhs = divides(m, max(pow(g, k) - 1, 0))
                require(lhs == rhs, f'guarded cast regression at {(m,g,k)}')
                cast_cases += 1
    # Explicit falsifier: dropping hg makes Nat's truncated subtraction unsound.
    guard_counterexample = {'m': 2, 'g': 0, 'k': 1,
                            'power_cast_eq_one': False, 'dvd_truncated_difference': True}
    require(residue_power(0, 1, 2) != 1 and divides(2, 0), 'guard falsifier failed')

    crt_cases = 0
    crt_zero_modulus_cases = 0
    for a in range(19):
        for b in range(19):
            if math.gcd(a, b) != 1:
                continue
            for x in range(19):
                for k in range(7):
                    lhs = finite_order(a*b, residue_power(x, k, a*b))
                    rhs = math.lcm(finite_order(a, residue_power(x, k, a)),
                                   finite_order(b, residue_power(x, k, b)))
                    require(lhs == rhs, f'CRT order regression at {(a,b,x,k)}')
                    crt_cases += 1
                    crt_zero_modulus_cases += (a*b == 0)

    prime_power_cases = 0
    for p in (3, 5, 7, 11, 13, 17, 19):
        for digit in range(1, min(p, 7)):
            g = 1 + p * digit
            require((g - 1) % p == 0 and (g - 1) % (p*p) != 0, 'LTE premises')
            for k in range(4):
                require(finite_order(p**(k+1), g) == p**k,
                        f'prime-power order regression at {(p,g,k)}')
                prime_power_cases += 1

    p, d, exponent = 120199, 47 * 2011, 94517 * (120199 - 1)
    require(d == 94517 and exponent == 11360754366, 'literal parameter mismatch')
    literal = {'prime_lift_residue': pow(2, exponent, p*p),
               'auxiliary_generator_residue': pow(2, exponent, p),
               'C0_generator_residue': pow(2, exponent, d*p),
               'fixed_generator_residue': pow(2, exponent, d)}
    require(literal == {'prime_lift_residue': 7300767062,
                       'auxiliary_generator_residue': 1,
                       'C0_generator_residue': 1, 'fixed_generator_residue': 1},
            'literal modular exponentiation mismatch')
    fact_cases = 0
    for dd in range(8):
        for pp in range(8):
            for k in range(8):
                require((dd*pp)*pp**k == dd*pp**(k+1), 'factorization regression')
                fact_cases += 1

    print(json.dumps({'status': 'PASS', 'lean_status': 'not run; all candidates uncompiled',
        'scope': 'Read-only source/patch checks and finite regressions; not proof of Lean elaboration',
        'source_pin': manifest['source_pin'], 'patches': rows,
        'net_physical_removed': total[0], 'net_nonblank_removed': total[1],
        'new_helpers': 0, 'removed_private_helpers': ['order_transport'],
        'finite_checks': {'guarded_cast_cases': cast_cases, 'guard_counterexample': guard_counterexample,
            'CRT_order_cases': crt_cases, 'CRT_zero_modulus_cases': crt_zero_modulus_cases,
            'odd_prime_power_order_cases': prime_power_cases,
            'modulus_factorization_cases': fact_cases, 'actual_modular_residues': literal},
        'upstream_snapshot_check': bool(args.upstream)}, indent=2))


if __name__ == '__main__':
    main()
