#!/usr/bin/env python3
"""Write explicit certificate/witness pairs for independent JSON verification."""
from __future__ import annotations
import json
from pathlib import Path
from priority_certificates import compile_block, as_inputs, from_fractions


def save_instance(circuit, inputs: dict[str, int], path: Path, description: str) -> None:
    values = circuit.witness(inputs)
    if circuit.value(values) != 0:
        raise AssertionError('The proposed instance is not certified')
    path.write_text(json.dumps({
        'description': description,
        'free_inputs': inputs,
        'values_in_exported_variable_order': values,
        'expected_polynomial_value': 0,
    }, indent=2) + '\n', encoding='utf-8')


def main() -> None:
    out = Path(__file__).resolve().parents[1] / 'results'
    out.mkdir(exist_ok=True)
    _, A, B = from_fractions([(1, 72), (3, 2)])
    c = compile_block(2, 2, [1], endpoint=True)
    c.export(out / 'example_certificate.json')
    save_instance(c, as_inputs(A, B, [5, 0], 2, [3, 2]),
                  out / 'example_instance.json',
                  'FRACTRAN (1/72,3/2): two copies of rule 2 take 32 to 72.')
    _, A, B = from_fractions([(3, 2)])
    k = 10**1000
    c = compile_block(1, 2, [0], endpoint=True, maximal=True)
    c.export(out / 'large_maximal_certificate.json')
    save_instance(c, as_inputs(A, B, [k, 7], k, [0, k+7]),
                  out / 'large_maximal_instance.json',
                  'FRACTRAN (3/2): exactly 10^1000 complete copies, in valuations.')
    print('Wrote two exact polynomial/witness pairs to', out)


if __name__ == '__main__':
    main()
