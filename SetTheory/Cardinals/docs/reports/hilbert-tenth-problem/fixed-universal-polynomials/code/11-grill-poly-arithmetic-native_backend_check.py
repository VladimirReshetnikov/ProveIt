# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Native identity replay through the compact binary source backend."""
import json
import random
from pathlib import Path
from compact_dag import DAG, ConstantPool, evaluate_mod
from native_history import build
from native_check import _receipt_eval
HERE = Path(__file__).resolve().parent

def check():
    fixtures = json.loads((HERE / 'native_receipt_fixtures.json').read_text())['fixtures']
    rng = random.Random(202610030854)
    results = []
    evaluations = 0
    for index, fixture in enumerate(fixtures):
        packet = fixture['packet']
        path = HERE / f'native_backend_small_{index}.bin'
        d = DAG(path)
        X = d.input('X', role='external')
        q = build(d, fixture['program'], X)
        squares = []
        for a, b in q['residuals']:
            r = d.sub(a, b)
            squares.append(d.mul(r, r))
        output = d.sub(d.mul(q['unit'], d.add(d.const(1), d.total(squares))), d.const(1))
        manifest = d.finish(output, {'native_metadata': q['metadata']})
        for prime in (1000000007, 1000000009, 2147483647, 2305843009213693951):
            for case in range(12):
                oldvalues = {n: rng.randrange(-7, 8) for n in packet['parameters'] + packet['auxiliaries']}
                old = _receipt_eval(packet, oldvalues, prime)
                residuals = [(old(a) - old(b)) % prime for a, b in packet['comparisons'][:-1]]
                expected = (old(packet['unit_register']) * (1 + sum((r * r for r in residuals))) - 1) % prime
                inputs = [None] * manifest['input_count']
                for entry in manifest['inputs']:
                    prefix = entry['name']
                    for i in range(entry['count']):
                        name = prefix + str(i) if entry.get('indexed') else prefix
                        oldname = 'x' if name == 'X' else name.removeprefix('native.')
                        inputs[entry['start'] + i] = oldvalues[oldname]
                if not None not in inputs:
                    raise RuntimeError('Invariant failed at original source line 38')
                actual = evaluate_mod(path, manifest, prime, inputs.__getitem__)
                if not actual == expected:
                    raise RuntimeError((fixture['program'], prime, case))
                evaluations += 1
        results.append({'program': fixture['program'], 'ledger': manifest['ledger'], 'source_sha256': manifest['source_sha256'], 'binary_evaluations_equal_to_pinned_receipt': 48})
    pool = ConstantPool()
    numeral_checks = 0
    for n in (0, 1, 2, 3, 7, 100, 511, 512, 2030, 275944):
        b = pool.recipe('pow2', 2 * n + 1)
        diff = pool.recipe('affine_slope_minus_one', n)
        offset = pool.recipe('affine_offset', n)
        for modulus in (2, 3, 4, 9, 1000000007, 2305843009213693951):
            expected_b = pow(2, 2 * n + 1, modulus)
            expected_d = 2 * ((pow(4, n, 3 * modulus) - 1) // 3) % modulus
            if not pool.value_mod(b, modulus) == expected_b:
                raise RuntimeError('Invariant failed at original source line 54')
            if not pool.value_mod(diff, modulus) == (expected_b - 1) % modulus:
                raise RuntimeError('Invariant failed at original source line 55')
            if not pool.value_mod(offset, modulus) == expected_d:
                raise RuntimeError('Invariant failed at original source line 56')
            numeral_checks += 3
    return {'status': 'PASS_NATIVE_COMPACT_BACKEND_IDENTITIES', 'upstream_code_executed': False, 'complete_binary_source_evaluations': evaluations, 'independent_numeral_checks': numeral_checks, 'fixtures': results}
if __name__ == '__main__':
    result = check()
    (HERE / 'native_backend_small_result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
