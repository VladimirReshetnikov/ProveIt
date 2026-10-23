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


def degree_block(circuit):
    degrees = {name: 1 for name in circuit['witnesses']}
    degrees.update({name: 0 for name in circuit['fixed_numerals']})
    lines = ['-- BEGIN GENERATED P76 DEGREE CERTIFICATE',
             '/-- A checked cancellation lowers the strong residual to degree32. -/',
             'theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :',
             '    (polynomial p).totalDegree ≤ 64 := by']
    for names, port in [(circuit['witnesses'], 'v'), (circuit['fixed_numerals'], 'p')]:
        for i, name in enumerate(names):
            expression = f'MvPolynomial.X ({i} : Fin 15)' if port == 'v' else f'MvPolynomial.C (p {i})'
            proof = f'by simp only [{name}, MvPolynomial.totalDegree_X, le_refl]' if port == 'v' else '(MvPolynomial.totalDegree_C _).le'
            lines.extend([f'  let {name} : MvPolynomial (Fin 15) ℤ := {expression}',
                          f'  have h_{name} : {name}.totalDegree ≤ {degrees[name]} := {proof}'])
    def gate(name, op, a, b, special=False):
        da, db = (0 if type(x) is int else degrees[x] for x in (a, b))
        degree = da + db if op == '*' else max(da, db)
        degrees[name] = degree
        lemma = {'+': 'degree_add', '-': 'degree_sub', '*': 'degree_mul'}[op]
        proofs = ['(degree_numeral ' + str(x) + ')' if type(x) is int else 'h_' + x for x in (a, b)]
        lines.append(f'  let {name} := {a} {op} {b}')
        if not special:
            lines.extend([f'  have h_{name} : {name}.totalDegree ≤ {degree} :=',
                          f'    {lemma} {proofs[0]} {proofs[1]}'])
    for name, op, a, b in circuit['source']:
        gate(name, op, a, b, name == 'strong_corrected_main')
        if name == 'strong_corrected_main':
            expansion = [
                ('degree_two_x', '*', 2, 'wn2'),
                ('degree_two_x_plus_one', '+', 'degree_two_x', 1),
                ('degree_y_square', '*', 'sn2', 'sn2'),
                ('degree_xy_square', '*', 'degree_two_x_plus_one', 'degree_y_square'),
                ('degree_inner', '+', 'degree_xy_square', 'a4m5'),
                ('degree_first', '*', 'degree_inner', 'c2'),
                ('degree_E_square', '*', 'UM', 'UM'),
                ('degree_E_eta', '*', 'degree_E_square', 'eta'),
                ('degree_two_kY', '*', 2, 'ksn2'),
                ('degree_two_kY_eta', '+', 'degree_two_kY', 'eta'),
                ('degree_second', '*', 'degree_E_eta', 'degree_two_kY_eta'),
                ('degree_n', '*', 'wn2', 'degree_y_square'),
                ('degree_k_square', '*', 'R10b', 'R10b'),
                ('degree_third', '*', 'degree_n', 'degree_k_square'),
                ('degree_sum', '+', 'degree_first', 'degree_second'),
                ('degree_diff', '-', 'degree_sum', 'degree_third'),
                ('degree_plus_tau', '+', 'degree_diff', 'tau_square'),
                ('degree_corrected', '-', 'degree_plus_tau', 1),
            ]
            for spec in expansion:
                gate(*spec)
            lines.extend(['  have correction_identity : strong_corrected_main = degree_corrected := by',
                          '    dsimp [strong_corrected_main, Ac2, A, a_square, a4m5, a4, R12, c2, R10a,',
                          '      residual_first, norm_first, first_product, first_root_base, first_next,',
                          '      ksn2, UM, tau_square, degree_corrected, degree_plus_tau, degree_diff,',
                          '      degree_sum, degree_first, degree_inner, degree_xy_square, degree_two_x_plus_one,',
                          '      degree_two_x, degree_y_square, degree_second, degree_E_eta, degree_E_square,',
                          '      degree_two_kY_eta, degree_two_kY, degree_third, degree_n, degree_k_square]',
                          '    ring',
                          '  have h_strong_corrected_main : strong_corrected_main.totalDegree ≤ 20 := by',
                          '    rw [correction_identity]', '    exact h_degree_corrected'])
            degrees[name] = 20
    lines.extend(['  change (value (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 64',
                  '  rw [← literalValue_eq_value]', '  change polynomial.totalDegree ≤ 64',
                  '  exact h_polynomial', '-- END GENERATED P76 DEGREE CERTIFICATE'])
    return '\n'.join(lines)


def main():
    circuit = build()
    DESTINATION.write_text(json.dumps(circuit, indent=2) + '\n')
    source = LEAN.read_text()
    for label, block in [('LITERAL EVALUATOR', literal_block(circuit)),
                         ('DEGREE CERTIFICATE', degree_block(circuit))]:
        begin, end = (f'-- {part} GENERATED P76 {label}' for part in ('BEGIN', 'END'))
        a, b = source.index(begin), source.index(end) + len(end)
        source = source[:a] + block + source[b:]
    LEAN.write_text(source)
    print(DESTINATION.relative_to(ROOT))

if __name__ == '__main__':
    main()
