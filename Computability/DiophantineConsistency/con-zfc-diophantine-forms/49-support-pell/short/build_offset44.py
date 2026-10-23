#!/usr/bin/env python3
"""Emit the double Pell-root-offset polynomial and its exact gate ledger.

Only construction and finite algebra are checked here.  Compiler semantics
remain the explicitly cited inherited ordinary/P67 proof interface.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'upstream/p69_unscaled.json'


def build(source):
    # Start from the literal normalized unscaled evaluator.  Preserve all
    # four fixed coefficient ports, the order of all unaffected witnesses,
    # and every unaffected producer.
    removed = {'norm_pair', 'norm_strong', 'strong_square_scaled',
               'norm_four', 'norm_product', 'all_units', 'seven_units',
               'polynomial', 'first_next', 'first_product', 'aux_y2',
               'H2', 'aux_square_gap', 'L17'}
    gates = []
    for original in source['source']:
        name, op, a, b = original
        if name in removed:
            continue
        if name == 'tau_square':
            gates.append(['offset_tau_square', '*', 'r', 'r'])
        elif name == 'norm_first':
            gates.extend([
                ['offset_tau_twice', '*', 2, 'r'],
                ['offset_tau_gap', '-', 'offset_tau_twice', 'R10b'],
                ['offset_tau_product', '*', 'first_root_base', 'offset_tau_gap'],
                ['norm_first', '+', 'offset_tau_square', 'offset_tau_product'],
            ])
        elif name == 'norm_aux':
            gates.extend([
                ['restored_y', '+', 'aux_u_rhs', 'u'],
                ['restored_y_square', '*', 'restored_y', 'restored_y'],
                ['offset_y_sum', '+', 'aux_u_rhs', 'restored_y'],
                ['offset_y_product', '*', 'u', 'offset_y_sum'],
                ['offset_y_scaled', '*', 'aux_reduced_coefficient', 'offset_y_product'],
                ['norm_aux', '-', 'restored_y_square', 'offset_y_scaled'],
            ])
        else:
            gates.append(original)
    gates.extend([
        ['first_index', '*', 'norm_first', 'norm_index'],
        ['main_transport', '*', 'norm_main', 'norm_transport'],
        ['residual_main_transport', '-', 'main_transport', 1],
        ['residual_aux', '-', 'norm_aux', 1],
        ['residual_strong', '-', 'R16', 'aux_reduced_coefficient'],
        ['residual_first_index', '-', 'first_index', 1],
        ['square_main_transport', '*', 'residual_main_transport', 'residual_main_transport'],
        ['square_aux', '*', 'residual_aux', 'residual_aux'],
        ['square_strong', '*', 'residual_strong', 'residual_strong'],
        ['square_first_index', '*', 'residual_first_index', 'residual_first_index'],
        ['sum_1', '+', 'square_main_transport', 'square_aux'],
        ['sum_2', '+', 'sum_1', 'square_strong'],
        ['polynomial', '+', 'sum_2', 'square_first_index'],
    ])
    witnesses = [('r' if v == 'tau' else 'u' if v == 'y' else v)
                 for v in source['witnesses']]
    return {
        'name': 'pell_root_offsets_15_positive_degree44',
        'witness_domain': 'strictly positive integers',
        'witnesses': witnesses,
        'fixed_numerals': source['fixed_numerals'],
        'source': gates,
        'output': 'polynomial',
        'coefficient_binding': {
            'file': '../coefficients/COEFFICIENT_BINDING.json',
            'aliases': {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
            'source_package': '31-sun10',
            'source_commit': '124c07c0b77a9e20e84676514d8b1ff78536ea3f',
            'warning': 'The four ports are rebound together to the coherent package-31 tuple. MF is shifted. This is a different fixed polynomial from the source package-36-bound circuit.'
        },
        'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'source_commit': '124c07c0b77a9e20e84676514d8b1ff78536ea3f',
        'source_path': 'Computability/DiophantineConsistency/circuits/p69_unscaled.json',
        'proof_boundary': 'New grouped evaluator of inherited root-gap constructions; no new checked Lean/Rocq or object-language ZFC derivation. Uses the whole package-31 coefficient tuple and inherited ordinary strong-norm compiler interface.',
    }


if __name__ == '__main__':
    result = build(json.loads(SOURCE.read_text()))
    (HERE / 'offset44.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Emitted', len(result['source']), 'operations')
