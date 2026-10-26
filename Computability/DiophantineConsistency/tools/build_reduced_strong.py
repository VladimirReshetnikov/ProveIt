#!/usr/bin/env python3
"""Emit the76-gate degree64 candidate and its literal Lean certificates."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'Computability/DiophantineConsistency'
SOURCE = DIRECTORY / 'circuits/p75_sos.json'
DESTINATION = DIRECTORY / 'circuits/p76_sos.json'
LEAN = DIRECTORY / 'Lean/DiophantineConsistency/ShortReducedStrong.lean'


def build():
    source = json.loads(SOURCE.read_text())
    gates = []
    for name, operation, left, right in source['source']:
        if name == 'residual_first':
            continue
        if name == 'norm_first':
            gates.append([name, operation, left, right])
            gates.append(['residual_first', '-', 'norm_first', 1])
        elif name == 'aux_coefficient_root':
            gates.append(['i_square', '*', 'i', 'i'])
        elif name == 'R16':
            gates.append(['strong_coefficient', '*', 'i_square', 'c2'])
            gates.append(['strong_corrected_main', '+', 'Ac2', 'residual_first'])
        elif name == 'strong_square_scaled':
            gates.append([name, '*', 'strong_coefficient', 'strong_corrected_main'])
        else:
            gates.append([name, operation, left, right])
    assert len(gates) == 76
    result = {**source, 'name': 'p76_corrected_strong_four_residual_sum_of_squares',
              'source': gates,
              'provenance': {'source': str(SOURCE.relative_to(ROOT)),
                  'sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                  'change': 'Add the already-computed first residual inside the strong norm; '
                            'factor its coefficient as i^2*c^2.'},
              'proof_boundary': 'ShortReducedStrong.lean checks the literal evaluator, '
                  'integer zero equivalence to P75, positive zero equivalence to P67, '
                  'and degree<=64. No native-window compiler is asserted.'}
    return result


def literal_block(circuit):
    lines = ['-- BEGIN GENERATED P76 LITERAL EVALUATOR',
             '/-- Literal evaluator of circuits/p76_sos.json, including every paid operation. -/',
             'def literalValue (p : Fin 4 → R) (v : Fin 15 → R) : R :=']
    for names, port in [(circuit['witnesses'], 'v'), (circuit['fixed_numerals'], 'p')]:
        lines.extend(f'  let {name} := {port} {i}' for i, name in enumerate(names))
    lines.extend(f'  let {name} := {a} {op} {b}' for name, op, a, b in circuit['source'])
    lines.extend(['  polynomial', '-- END GENERATED P76 LITERAL EVALUATOR'])
    return '\n'.join(lines)


def main():
    circuit = build()
    DESTINATION.write_text(json.dumps(circuit, indent=2) + '\n')
    source = LEAN.read_text()
    for label, block in [('LITERAL EVALUATOR', literal_block(circuit))]:
        begin, end = (f'-- {part} GENERATED P76 {label}' for part in ('BEGIN', 'END'))
        a, b = source.index(begin), source.index(end) + len(end)
        source = source[:a] + block + source[b:]
    LEAN.write_text(source)
    print(DESTINATION.relative_to(ROOT))

if __name__ == '__main__':
    main()
