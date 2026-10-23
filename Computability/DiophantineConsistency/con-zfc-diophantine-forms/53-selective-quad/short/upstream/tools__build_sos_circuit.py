#!/usr/bin/env python3
"""Emit the 75/77-operation residual circuits and literal Lean certificates."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DIRECTORY = ROOT / 'Computability/DiophantineConsistency'
SOURCE = DIRECTORY / 'circuits/p69_unscaled.json'
DESTINATION = DIRECTORY / 'circuits/p77_sos.json'
LEAN = DIRECTORY / 'Lean/DiophantineConsistency/ShortSystem.lean'
BEGIN = '-- BEGIN GENERATED P77 LITERAL EVALUATOR'
END = '-- END GENERATED P77 LITERAL EVALUATOR'
DEGREE_BEGIN = '-- BEGIN GENERATED P77 DEGREE CERTIFICATE'
DEGREE_END = '-- END GENERATED P77 DEGREE CERTIFICATE'


def build(compact=False):
    source = json.loads(SOURCE.read_text())
    removed = {'norm_pair', 'norm_strong', 'norm_four', 'norm_product',
               'all_units', 'seven_units', 'polynomial'}
    gates = [row for row in source['source'] if row[0] not in removed]
    if compact:
        gates.extend([['main_index', '*', 'norm_main', 'norm_index'],
                      ['main_index_transport', '*', 'main_index', 'norm_transport']])
        residuals = ['residual_first', 'residual_aux', 'residual_strong', 'residual_main_index_transport']
        residual_specs = [('residual_first', 'norm_first', 1), ('residual_aux', 'norm_aux', 1),
                          ('residual_strong', 'aux_f2_minus_one', 'strong_square_scaled'),
                          ('residual_main_index_transport', 'main_index_transport', 1)]
    else:
        gates.append(['index_transport', '*', 'norm_index', 'norm_transport'])
        residuals = ['residual_first', 'residual_main', 'residual_aux',
                     'residual_strong', 'residual_index_transport']
        residual_specs = [('residual_first', 'norm_first', 1), ('residual_main', 'norm_main', 1),
                          ('residual_aux', 'norm_aux', 1),
                          ('residual_strong', 'aux_f2_minus_one', 'strong_square_scaled'),
                          ('residual_index_transport', 'index_transport', 1)]
    gates.extend([[name, '-', left, right] for name, left, right in residual_specs])
    gates.extend([[name + '_square', '*', name, name] for name in residuals])
    previous = residuals[0] + '_square'
    for index, residual in enumerate(residuals[1:], 1):
        name = 'sum_' + str(index) if index < len(residuals) - 1 else 'polynomial'
        gates.append([name, '+', previous, residual + '_square'])
        previous = name
    assert len(gates) == (75 if compact else 77)
    result = dict(
        name='p75_four_residual_sum_of_squares' if compact else 'p77_five_residual_sum_of_squares',
        witness_domain=source['witness_domain'],
        witnesses=source['witnesses'], fixed_numerals=source['fixed_numerals'],
        source=gates, output='polynomial', coefficient_binding=source['coefficient_binding'],
        provenance=dict(source=str(SOURCE.relative_to(ROOT)),
                        sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                        change='Replace the unit product by five squared residuals; '
                               'share f^2-1 in the strong residual and prune norm_pair/norm_strong.'),
        proof_boundary='ShortSystem.lean certifies this literal evaluator and local positive zero '
                       'equivalence to P67. The native-window compiler is not certified here.',
    )
    return result


def lean_block(circuit):
    compact = len(circuit['source']) == 75
    count = 75 if compact else 77
    begin, end = (marker.replace('77', str(count)) for marker in (BEGIN, END))
    name = 'compactLiteralValue' if compact else 'literalValue'
    lines = [begin,
             f'/-- Literal evaluator of circuits/p{count}_sos.json; no implicit abbreviation costs. -/',
             f'def {name} (p : Fin 4 → R) (v : Fin 15 → R) : R :=']
    for names, port in [(circuit['witnesses'], 'v'), (circuit['fixed_numerals'], 'p')]:
        lines.extend(f'  let {name} := {port} {index}' for index, name in enumerate(names))
    lines.extend(f'  let {name} := {left} {operation} {right}'
                 for name, operation, left, right in circuit['source'])
    lines.extend(['  polynomial', end])
    return '\n'.join(lines)


def degree_block(circuit):
    compact = len(circuit['source']) == 75
    count = 75 if compact else 77
    begin, end = (marker.replace('77', str(count)) for marker in (DEGREE_BEGIN, DEGREE_END))
    polynomial = 'compactPolynomial' if compact else 'polynomial'
    value = 'compactValue' if compact else 'value'
    equality = 'compactLiteralValue_eq_compactValue' if compact else 'literalValue_eq_value'
    degrees = {name: 1 for name in circuit['witnesses']}
    degrees.update({name: 0 for name in circuit['fixed_numerals']})
    lines = [begin,
             '/-- A kernel-checked upper degree bound for the actual polynomial. -/',
             f'theorem {polynomial}_totalDegree_le (p : Fin 4 → ℤ) :',
             f'    ({polynomial} p).totalDegree ≤ 68 := by']
    for names, port in [(circuit['witnesses'], 'X'), (circuit['fixed_numerals'], 'p')]:
        for index, name in enumerate(names):
            expression = f'MvPolynomial.X ({index} : Fin 15)' if port == 'X' else f'MvPolynomial.C (p {index})'
            proof = f'by simp only [{name}, MvPolynomial.totalDegree_X, le_refl]' if port == 'X' else \
                '(MvPolynomial.totalDegree_C _).le'
            lines.extend([f'  let {name} : MvPolynomial (Fin 15) ℤ := {expression}',
                          f'  have h_{name} : {name}.totalDegree ≤ {degrees[name]} := {proof}'])
    for name, operation, left, right in circuit['source']:
        dl, dr = (0 if type(x) is int else degrees[x] for x in (left, right))
        degree = dl + dr if operation == '*' else max(dl, dr)
        degrees[name] = degree
        lemma = {'+': 'degree_add', '-': 'degree_sub', '*': 'degree_mul'}[operation]
        proofs = ['(degree_numeral ' + str(x) + ')' if type(x) is int else 'h_' + x for x in (left, right)]
        lines.extend([f'  let {name} := {left} {operation} {right}',
                      f'  have h_{name} : {name}.totalDegree ≤ {degree} :=',
                      f'    {lemma} {proofs[0]} {proofs[1]}'])
    lines.extend([f'  change ({value} (fun j => MvPolynomial.C (p j)) MvPolynomial.X).totalDegree ≤ 68',
                  f'  rw [← {equality}]',
                  '  change polynomial.totalDegree ≤ 68',
                  '  exact h_polynomial', end])
    return '\n'.join(lines)


def emit(compact=False):
    circuit = build(compact)
    count = 75 if compact else 77
    destination = DESTINATION.with_name(f'p{count}_sos.json')
    destination.write_text(json.dumps(circuit, indent=2) + '\n')
    source = LEAN.read_text()
    block = lean_block(circuit)
    begin, end = (marker.replace('77', str(count)) for marker in (BEGIN, END))
    if begin in source:
        a, b = source.index(begin), source.index(end) + len(end)
        source = source[:a] + block + source[b:]
    else:
        marker = '/-- Ring homomorphisms preserve the complete five-equation expression. -/'
        source = source.replace(marker, block + '\n\n' + marker)
    degree = degree_block(circuit)
    begin, end = (marker.replace('77', str(count)) for marker in (DEGREE_BEGIN, DEGREE_END))
    if begin in source:
        a, b = source.index(begin), source.index(end) + len(end)
        source = source[:a] + degree + source[b:]
    else:
        source = source.replace('end DiophantineConsistency.ShortSystem',
                                degree + '\n\nend DiophantineConsistency.ShortSystem')
    LEAN.write_text(source)
    print(str(destination.relative_to(ROOT)))


if __name__ == '__main__':
    emit(False)
    emit(True)

