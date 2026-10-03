"""Bounded binding wrapper and semantic tamper tests; all checks survive -O."""
import copy
import json
from pathlib import Path
import check_example as binding
import example_emitter as emitter
import independent_expansion as independent

HERE = Path(__file__).resolve().parent


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def bounded_binding(data, witness):
    independent.preflight(data, witness)
    result = binding.check_artifact(data, witness)
    inputs = data['input_values']
    circuit, _, _ = emitter.build(inputs[0] - inputs[1], inputs[2] + 1, data['T'], data['K'], data['target'])
    require(binding.strict_equal(witness, circuit.values[circuit.input_count:]), 'canonical regenerated witness mismatch')
    independent.check(data, witness)
    return result


def must_reject(fn, detail):
    try:
        fn()
    except (ValueError, TypeError, KeyError, IndexError):
        return
    raise RuntimeError('accepted mutation: ' + detail)


def main():
    data = independent.read_json(HERE / 'example-polynomial.json')
    witness = independent.read_json(HERE / 'example-witness.json')
    bounded_binding(data, witness)
    changes = [
        ('source', {}), ('T', 2), ('K', 1), ('target', [0, 1]),
        ('input_count', True), ('input_values', [0, 10, 5]),
        ('variable_names', ['wrong'] + data['variable_names'][1:]),
        ('residuals', data['residuals'][:-1]), ('expanded_quartic', data['expanded_quartic'][:-1]),
        ('output', [-8, -3]), ('rounds', []), ('ledger', {}),
        ('T', independent.MAX_ROUNDS + 1), ('K', 10 ** 100),
        ('input_values', [0, 1 << (independent.MAX_BITS + 1), 4]),
    ]
    for name, value in changes:
        bad = copy.deepcopy(data)
        bad[name] = value
        must_reject(lambda: bounded_binding(bad, witness), name)
    for value in (True, 1.0, -1, 1 << (independent.MAX_BITS + 1)):
        wrong = list(witness)
        wrong[0] = value
        must_reject(lambda: bounded_binding(data, wrong), 'witness exact domain')
    wrong = list(witness)
    wrong[0] += 1
    must_reject(lambda: bounded_binding(data, wrong), 'witness nonzero')
    bad = copy.deepcopy(data)
    bad['expanded_quartic'][0][0] += 1
    must_reject(lambda: independent.check(bad, witness), 'independent expansion coefficient')
    bad = copy.deepcopy(data)
    bad['residuals'][0][0][0] += 1
    must_reject(lambda: independent.check(bad, witness), 'independent residual coefficient')
    bad = copy.deepcopy(data)
    bad['expanded_quartic'].append(bad['expanded_quartic'][0])
    must_reject(lambda: independent.check(bad, witness), 'duplicate expanded monomial')
    # Both polynomial lists zeroed coherently would pass a bare expansion identity,
    # but the normative compiler binding must reject the invented zero polynomial.
    bad = copy.deepcopy(data)
    bad['residuals'] = []
    bad['expanded_quartic'] = []
    must_reject(lambda: bounded_binding(bad, witness), 'invented polynomial with matching expansion')
    result = dict(status='passed', optimized=not __debug__, declaration_mutations=len(changes),
                  malformed_or_changed_witnesses=5, independent_polynomial_mutations=3,
                  invented_bound_polynomial_rejected=True,
                  practical_limits=dict(rounds=independent.MAX_ROUNDS, integer_bits=independent.MAX_BITS,
                                        variables=independent.MAX_VARIABLES, residuals=independent.MAX_ROWS))
    (HERE / 'artifact-checks-receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
