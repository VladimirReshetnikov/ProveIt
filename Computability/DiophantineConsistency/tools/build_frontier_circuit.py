#!/usr/bin/env python3
"""Emit P73 and its literal Lean evaluator and degree-80 certificate."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'Computability/DiophantineConsistency'
SOURCE = DIRECTORY / 'circuits/p69_unscaled.json'
DESTINATION = DIRECTORY / 'circuits/p73_sos.json'
LEAN = DIRECTORY / 'Lean/DiophantineConsistency/ShortFrontier.lean'


def build():
    source = json.loads(SOURCE.read_text())
    removed = {'norm_pair', 'norm_strong', 'norm_four', 'norm_product',
               'all_units', 'seven_units', 'polynomial'}
    gates = [row for row in source['source'] if row[0] not in removed]
    gates.extend([
        ['first_main', '*', 'norm_first', 'norm_main'],
        ['aux_index', '*', 'norm_aux', 'norm_index'],
        ['aux_index_transport', '*', 'aux_index', 'norm_transport'],
        ['residual_first_main', '-', 'first_main', 1],
        ['residual_aux_index_transport', '-', 'aux_index_transport', 1],
        ['residual_strong', '-', 'aux_f2_minus_one', 'strong_square_scaled'],
        ['first_main_square', '*', 'residual_first_main', 'residual_first_main'],
        ['aux_index_transport_square', '*', 'residual_aux_index_transport', 'residual_aux_index_transport'],
        ['strong_residual_square', '*', 'residual_strong', 'residual_strong'],
        ['partial_sum', '+', 'first_main_square', 'aux_index_transport_square'],
        ['polynomial', '+', 'partial_sum', 'strong_residual_square'],
    ])
    assert len(gates) == 73
    return dict(name='p73_three_grouped_residuals', witness_domain=source['witness_domain'],
                witnesses=source['witnesses'], fixed_numerals=source['fixed_numerals'],
                source=gates, output='polynomial', coefficient_binding=source['coefficient_binding'],
                provenance=dict(source=str(SOURCE.relative_to(ROOT)),
                                sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                                change='Three squared grouped residuals; share f^2-1 in the strong residual.'),
                proof_boundary='ShortFrontier.lean certifies this literal evaluator, degree <=80 '
                               'and local positive zero equivalence to P67, without a native-window compiler theorem.')


def bindings(circuit, polynomial=False):
    lines = []
    for names, port in [(circuit['witnesses'], 'v'), (circuit['fixed_numerals'], 'p')]:
        for index, name in enumerate(names):
            if polynomial:
                term = f'MvPolynomial.X ({index} : Fin 15)' if port == 'v' else f'MvPolynomial.C (p {index})'
                proof = f'by simp only [{name}, MvPolynomial.totalDegree_X, le_refl]' if port == 'v' else \
                    '(MvPolynomial.totalDegree_C _).le'
                lines.extend([f'  let {name} : MvPolynomial (Fin 15) ℤ := {term}',
                              f'  have h_{name} : {name}.totalDegree ≤ {1 if port == "v" else 0} := {proof}'])
            else:
                lines.append(f'  let {name} := {port} {index}')
    return lines


def literal(circuit):
    return '\n'.join(['-- BEGIN GENERATED P73 LITERAL EVALUATOR',
                      'def literalValue (p : Fin 4 → R) (v : Fin 15 → R) : R :='] +
                     bindings(circuit) +
                     [f'  let {name} := {left} {op} {right}' for name, op, left, right in circuit['source']] +
                     ['  polynomial', '-- END GENERATED P73 LITERAL EVALUATOR'])


def degree(circuit):
    bounds = {name: 1 for name in circuit['witnesses']}
    bounds.update({name: 0 for name in circuit['fixed_numerals']})
    lines = ['-- BEGIN GENERATED P73 DEGREE CERTIFICATE',
             'theorem polynomial_totalDegree_le (p : Fin 4 → ℤ) :',
             '    (polynomial p).totalDegree ≤ 80 := by'] + bindings(circuit, True)
    for name, op, left, right in circuit['source']:
        a, b = (0 if type(x) is int else bounds[x] for x in (left, right))
        bound = a + b if op == '*' else max(a, b)
        lines.append(f'  let {name} := {left} {op} {right}')
        if name == 'norm_main':
            bound = 18
            lines.extend([
                '  have h_norm_main : norm_main.totalDegree ≤ 18 := by',
                '    have hform : norm_main = (R12 * R10a + wn2 + gam) ^ 2 - (R12 ^ 2 + a4m5) * R10a ^ 2 := by',
                '      dsimp only [norm_main, L15, R14, D1, cam2, Ac2, A, a_square, c2]',
                '      ring',
                '    rw [hform]',
                '    exact degree_main_norm h_R12 h_R10a h_wn2 h_gam h_a4m5',
            ])
        else:
            lemma = {'+': 'degree_add', '-': 'degree_sub', '*': 'degree_mul'}[op]
            proofs = ['(degree_numeral ' + str(x) + ')' if type(x) is int else 'h_' + x for x in (left, right)]
            lines.extend([f'  have h_{name} : {name}.totalDegree ≤ {bound} :=',
                          f'    {lemma} {proofs[0]} {proofs[1]}'])
        bounds[name] = bound
    assert bounds['polynomial'] == 80
    lines.extend(['  change (value (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 80',
                  '  rw [← literalValue_eq_value]',
                  '  change polynomial.totalDegree ≤ 80',
                  '  exact h_polynomial', '-- END GENERATED P73 DEGREE CERTIFICATE'])
    return '\n'.join(lines)


if __name__ == '__main__':
    circuit = build()
    DESTINATION.write_text(json.dumps(circuit, indent=2) + '\n')
    text = LEAN.read_text()
    for kind, block in [('LITERAL EVALUATOR', literal(circuit)), ('DEGREE CERTIFICATE', degree(circuit))]:
        begin, end = '-- BEGIN GENERATED P73 ' + kind, '-- END GENERATED P73 ' + kind
        a, b = text.index(begin), text.index(end) + len(end)
        text = text[:a] + block + text[b:]
    LEAN.write_text(text)
    print(DESTINATION.relative_to(ROOT))
