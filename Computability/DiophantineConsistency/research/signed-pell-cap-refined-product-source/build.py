#!/usr/bin/env python3
"""SOURCE ONLY, on HOLD until both full reviews and explicit root release."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/signed-pell-cap-refined-source'
ORDINARY = ROOT / 'research/signed-pell-cap-refined-scalar-product'
PARENT_SEAL = '73a5b427338c33cb5ff0365fc64a994b796b16837d9bdc2a987d63d5eef8ed51'
ORDINARY_SEAL = 'be2a7ff725502344d862af1fdca0744fc64272840ec8947f214b7deee3773b0e'
OMIT = {1, 6, 7, 8, 9, 10, 11, 12, 13, 14}
CHRONOLOGY = ['temporary_helper_normalization', 'absolute_frame_and_nonzero_t',
              'signed_A_primary_pool', 'q_support_at_t', 'same_pair_base_one_then_F',
              'four_q_power_denominators', 'successor_residues_and_signed_indices',
              'reciprocal_last_scalar', 'strict_eight_factor_product',
              'restore_graphs_on_original_unnormalized_body', 'refined_calibration']


def need(ok, text):
    if not ok:
        raise ValueError(text)


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def terms(items):
    result = {}
    for coefficient, monomial in items:
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + coefficient
    return [[c, list(m)] for m, c in sorted(result.items()) if c]


def moved(items, mapping):
    return terms([[c, [mapping[i] for i in m]] for c, m in items])


def graph(expression, auxiliary):
    a, b, c = auxiliary
    return terms(expression + [[-1, [a, a]], [-1, [b, b]], [-1, [c, c]], [-1, [c]]])


def authenticate():
    pins = read(HERE / 'SOURCE_PINS.json')
    for section, base in [('files', ROOT), ('core', HERE)]:
        for name, expected in pins[section].items():
            need(digest(base / name) == expected, 'whole pinned file ' + name)
    for name, expected in pins['closed_dependencies'].items():
        directory = ROOT / name
        need(digest(directory / 'MANIFEST.json') == expected, 'closed seal ' + name)
        actual = {str(p.relative_to(directory)): digest(p) for p in directory.rglob('*')
                  if p.is_file() and p != directory / 'MANIFEST.json'}
        need(read(directory / 'MANIFEST.json')['files'] == actual, 'closed inventory ' + name)
    need(pins['closed_dependencies'].get(str(PARENT.relative_to(ROOT))) == PARENT_SEAL,
         'exact refined parent seal')
    need(pins['closed_dependencies'].get(str(ORDINARY.relative_to(ROOT))) == ORDINARY_SEAL,
         'exact complete ordinary scalar-product seal')
    if (HERE / 'MANIFEST.json').exists():
        actual = {str(p.relative_to(HERE)): digest(p) for p in HERE.rglob('*')
                  if p.is_file() and p != HERE / 'MANIFEST.json'}
        need(read(HERE / 'MANIFEST.json')['files'] == actual, 'complete sealed product packet')
    return pins


def produce():
    authenticate()
    body, old, domain = [read(PARENT / n) for n in ['source.json', 'guarded.json', 'domain.json']]
    interface = read(ORDINARY / 'INTERFACE.json')
    parent_plan = read(PARENT / 'TRANSFORM.json')
    need(len(body['variables']) == 399 and len(body['residuals']) == 334, 'whole body boundary')
    removed = [g for g in domain['guards'] if g.get('original_guard_index') in OMIT]
    need(removed == interface['omitted_graphs'] and len(removed) == 10, 'exact ten graph policy')
    rows, variables = copy.deepcopy(body['residuals']), copy.deepcopy(body['variables'])
    products = []
    for j in range(2, 9):
        coordinate, row = len(variables), len(rows)
        variables.append(dict(name='scalar_product.p' + str(j), kind='gate'))
        if j == 2:
            rhs = [[-1, []], [-1, [16]], [-1, [17]], [-1, [16, 17]]]
        else:
            rhs = [[-1, [coordinate - 1]], [-1, [15 + j, coordinate - 1]]]
        rows.append(dict(label='scalar_product.p' + str(j) + '_definition',
                         terms=terms([[1, [coordinate]]] + rhs)))
        products.append(dict(name='p' + str(j), coordinate=coordinate, row=row))
    source = dict(schema='refined_cap_scalar_product_body_v1', domain='unrestricted integers',
                  variant='refined_signed_cap_eight_factor_scalar_product_source_only',
                  polynomial='sum of squares of all residuals', variables=variables, residuals=rows,
                  parent_source_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL)
    guarded = copy.deepcopy(source)
    vm = {i: i for i in range(399)}
    rm = {i: i for i in range(334)}
    guards = []
    for spec in domain['guards']:
        if spec.get('original_guard_index') in OMIT:
            continue
        new = copy.deepcopy(spec)
        if all(i < 399 for i in spec['auxiliary']):
            need(spec['row'] < 334, 'embedded graph remains in whole body')
        else:
            auxiliary = list(range(len(guarded['variables']), len(guarded['variables']) + 3))
            vm.update(zip(spec['auxiliary'], auxiliary))
            new.update(auxiliary=auxiliary, row=len(guarded['residuals']))
            rm[spec['row']] = new['row']
            guarded['variables'] += [copy.deepcopy(old['variables'][i]) for i in spec['auxiliary']]
            guarded['residuals'].append(dict(label=old['residuals'][spec['row']]['label'],
                                           terms=graph(new['expression'], auxiliary)))
        guards.append(new)
    removed_aux = sorted(i for g in removed for i in g['auxiliary'])
    removed_rows = {g['row'] for g in removed}
    occurrences = {}
    for spec in removed:
        for v in spec['auxiliary']:
            hits = [i for i, row in enumerate(old['residuals']) if any(v in m for c, m in row['terms'])]
            need(hits == [spec['row']], 'whole omitted-witness privacy')
            occurrences[str(v)] = hits
    auxiliary = list(range(len(guarded['variables']), len(guarded['variables']) + 3))
    product_guard = dict(kind='strict_index_product', expression=[[-1, []], [1, [405]]],
                         product_coordinate=405, factors=[dict(coordinate=i, shift=1) for i in range(16, 24)],
                         auxiliary=auxiliary, row=len(guarded['residuals']))
    guarded['variables'] += [dict(name='scalar_product_positive.' + s, kind='integer_guard')
                             for s in ['a', 'b', 'c']]
    guarded['residuals'].append(dict(label='domain_guard.scalar_product_positive',
                                    terms=graph(product_guard['expression'], auxiliary)))
    guards.append(product_guard)
    need(len({v['name'] for v in guarded['variables']}) == len(guarded['variables']), 'fresh unique names')
    need(set(vm) == set(range(len(old['variables']))) - set(removed_aux), 'whole old coordinate namespace')
    need(set(rm) == set(range(len(old['residuals']))) - removed_rows, 'whole old row namespace')
    for old_row, new_row in rm.items():
        need(moved(old['residuals'][old_row]['terms'], vm) == guarded['residuals'][new_row]['terms'],
             'complete old residual identity')
    plan = dict(schema='refined_cap_scalar_product_literal_map_v1',
                parent_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL,
                old_body_to_new=[[i, i] for i in range(399)],
                old_guarded_to_new=[[i, vm[i]] for i in sorted(vm)],
                old_row_to_new=[dict(old_row=i, new_row=rm.get(i),
                                    status='omitted_scalar_graph' if i in removed_rows else 'identical')
                                for i in range(len(old['residuals']))],
                omitted_original_guard_indices=sorted(OMIT), removed_graphs=removed,
                removed_private_coordinates=removed_aux, complete_omitted_auxiliary_occurrences=occurrences,
                product_gates=products, new_product_graph=product_guard,
                all18_actual_power_requests=copy.deepcopy(interface['all18_actual_power_requests']),
                all15_signed_targets=copy.deepcopy(parent_plan['all_original_seeds']),
                all37_frame_atoms=copy.deepcopy(parent_plan['all37_frame_atoms']),
                native_front_parent=parent_plan['native_front_new'], native_front_new=parent_plan['native_front_new'],
                helper_reflection=parent_plan['reflection'], helper_normalization_is_temporary=True,
                whole_refined_body_pointwise_fixed=True, retained_witness_values_preserved_under_map=True,
                h_changes_in_product_maps=False, A_or_C_positive_assumed=False,
                chronology=CHRONOLOGY, optimizer_factorization_projection_executed=False,
                accepted_projected_frontier_claim=False)
    artifacts = {'source.json': source, 'guarded.json': guarded,
                 'domain.json': dict(schema='refined_cap_scalar_product_domain_v1', guards=guards),
                 'TRANSFORM.json': plan}
    artifacts['CALIBRATION_BINDING.json'] = dict(
        schema='refined_cap_product_ordinary_source_calibration_v1',
        parent_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL,
        parent_calibration_sha256=digest(PARENT / 'CALIBRATION_BINDING.json'),
        source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
        generated_source_files={n: hashlib.sha256(encoded(x)).hexdigest() for n, x in artifacts.items()},
        formal_native_contracts=read(PARENT / 'CALIBRATION_BINDING.json')['formal_native_contracts'],
        native_front_parent=parent_plan['native_front_new'], native_front_new=parent_plan['native_front_new'],
        witness_maps='Keep original unnormalized refined body and retained witnesses; restore ten old triples, or adjoin exact products and their strict graph. Both maps keep h and signed A/C.',
        ordinary_soundness_and_positive_completeness='Compose sealed pointwise refined scalar-product theorem with complete sealed refined-source calibration only after restoring its ten graph rows.',
        whole_refined_body_pointwise_fixed=True, new_formal_Lean_theorem_claimed=False,
        optimizer_factorization_projection_or_quartic_executed=False)
    return artifacts


def protected(path):
    target = path.resolve()
    return any(target.is_relative_to((ROOT / n).resolve())
               for n in read(HERE / 'SOURCE_PINS.json')['closed_dependencies'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--destination', type=Path, default=HERE)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    need(not protected(args.destination) and not protected(args.output), 'never write a closed dependency')
    artifacts = produce()
    for name, value in artifacts.items():
        target, data = args.destination / name, encoded(value)
        if args.check:
            need(target.read_bytes() == data, 'pure deterministic source check ' + name)
        else:
            need(not (HERE / 'MANIFEST.json').exists(), 'sealed packet is immutable')
            need(not target.is_symlink() and (not target.exists() or target.read_bytes() == data),
                 'refuse different existing source ' + name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), pure_check=args.check,
                  source_only=True, source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  generated={n: hashlib.sha256(encoded(v)).hexdigest() for n, v in artifacts.items()},
                  optimizer_factorization_projection_executed=False)
    data = encoded(result)
    need(not args.output.is_symlink() and (not args.output.exists() or args.output.read_bytes() == data),
         'refuse different existing receipt')
    need(not (HERE / 'MANIFEST.json').exists() or not args.output.resolve().is_relative_to(HERE),
         'receipt must be outside a sealed packet')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()
