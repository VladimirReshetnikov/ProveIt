#!/usr/bin/env python3
"""Nine-factor SOURCE ONLY materializer; CODE ONLY/HOLD for both full reviews."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/signed-pell-cap-refined-product-source'
ORDINARY = ROOT / 'research/signed-pell-cap-nine-factor-fused'
PARENT_SEAL = 'de311c82c61e7fee99e816c971256d662a28e620c51807ca7d5ef3611240ea93'
ORDINARY_SEAL = '836c87b375d2049c44548e999a9b271b40805211bcbb5f01678f108a2c53a60d'


def need(ok, why):
    if not ok:
        raise ValueError(why)


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def terms(items):
    result = {}
    for c, m in items:
        key = tuple(sorted(m))
        result[key] = result.get(key, 0) + c
    return [[c, list(m)] for m, c in sorted(result.items()) if c]


def graph(expression, auxiliary):
    a, b, c = auxiliary
    return terms(expression + [[-1, [a, a]], [-1, [b, b]], [-1, [c, c]], [-1, [c]]])


def moved(items, mapping):
    return terms([[c, [mapping[i] for i in m]] for c, m in items])


def authenticate():
    pins = read(HERE / 'SOURCE_PINS.json')
    for section, base in [('files', ROOT), ('core', HERE)]:
        for name, expected in pins[section].items():
            need(digest(base / name) == expected, 'whole pinned file ' + name)
    for name, expected in pins['closed_dependencies'].items():
        folder = ROOT / name
        need(digest(folder / 'MANIFEST.json') == expected, 'closed seal ' + name)
        declared = read(folder / 'MANIFEST.json')['files']
        actual = {str(p.relative_to(folder)): digest(p) for p in folder.rglob('*')
                  if p.is_file() and p != folder / 'MANIFEST.json'}
        members = {n: dict(bytes=(folder / n).stat().st_size, sha256=h)
                   if isinstance(declared.get(n), dict) else h for n, h in actual.items()}
        need(declared == members, 'complete closed inventory ' + name)
    need(pins['closed_dependencies'].get(str(PARENT.relative_to(ROOT))) == PARENT_SEAL,
         'exact whole product source seal')
    need(pins['closed_dependencies'].get(str(ORDINARY.relative_to(ROOT))) == ORDINARY_SEAL,
         'exact whole ordinary fused-nine theorem seal')
    if (HERE / 'MANIFEST.json').exists():
        actual = {str(p.relative_to(HERE)): digest(p) for p in HERE.rglob('*')
                  if p.is_file() and p != HERE / 'MANIFEST.json'}
        need(read(HERE / 'MANIFEST.json')['files'] == actual, 'complete sealed new packet')
    return pins


def produce():
    authenticate()
    body, old, domain = [read(PARENT / n) for n in ['source.json', 'guarded.json', 'domain.json']]
    interface = read(ORDINARY / 'INTERFACE.json')
    need(len(body['variables']) == 406 and len(body['residuals']) == 341, 'complete parent body')
    removed = [g for g in domain['guards'] if g.get('coordinate') == 11 or g['kind'] == 'strict_index_product']
    need(removed == interface['removed_parent_graphs'], 'exact two parent graphs')
    source = dict(schema='refined_cap_nine_factor_body_v1', domain='unrestricted integers',
                  variant='refined_signed_cap_fused_nine_factor_source_only',
                  polynomial='sum of squares of all residuals',
                  variables=copy.deepcopy(body['variables']), residuals=copy.deepcopy(body['residuals']),
                  parent_source_manifest_sha256=PARENT_SEAL, ordinary_manifest_sha256=ORDINARY_SEAL)
    guarded = copy.deepcopy(source)
    vm, rm = {i: i for i in range(406)}, {i: i for i in range(341)}
    guards = []
    for spec in domain['guards']:
        if spec in removed:
            continue
        new = copy.deepcopy(spec)
        if spec['row'] < 341:
            need(all(i < 406 for i in spec['auxiliary']), 'embedded graph stays in body')
        else:
            auxiliary = list(range(len(guarded['variables']), len(guarded['variables']) + 3))
            vm.update(zip(spec['auxiliary'], auxiliary))
            new.update(row=len(guarded['residuals']), auxiliary=auxiliary)
            rm[spec['row']] = new['row']
            guarded['variables'] += [copy.deepcopy(old['variables'][i]) for i in spec['auxiliary']]
            guarded['residuals'].append(dict(label=old['residuals'][spec['row']]['label'],
                                           terms=graph(new['expression'], auxiliary)))
        guards.append(new)
    auxiliary = list(range(len(guarded['variables']), len(guarded['variables']) + 3))
    mixed = dict(kind='strict_fused_index_endpoint_product',
                 expression=[[-1, []], [1, [11, 405]], [1, [405]]],
                 existing_partial_product_coordinate=405,
                 factors=[dict(coordinate=i, shift=1) for i in [11] + list(range(16, 24))],
                 auxiliary=auxiliary, row=len(guarded['residuals']))
    guarded['variables'] += [dict(name='nine_factor_positive.' + s, kind='integer_guard')
                             for s in ['a', 'b', 'c']]
    guarded['residuals'].append(dict(label='domain_guard.nine_factor_positive',
                                    terms=graph(mixed['expression'], auxiliary)))
    guards.append(mixed)
    dropped_aux = sorted(i for g in removed for i in g['auxiliary'])
    dropped_rows = {g['row'] for g in removed}
    occurrences = {str(v): [i for i, r in enumerate(old['residuals']) if any(v in m for c, m in r['terms'])]
                   for v in dropped_aux}
    need(all(occurrences[str(v)] == [g['row']] for g in removed for v in g['auxiliary']),
         'whole removed graph witness privacy')
    need(set(vm) == set(range(len(old['variables']))) - set(dropped_aux), 'whole old coordinate map')
    need(set(rm) == set(range(len(old['residuals']))) - dropped_rows, 'whole old row map')
    for i, j in rm.items():
        expected = copy.deepcopy(old['residuals'][i])
        expected['terms'] = moved(expected['terms'], vm)
        need(expected == guarded['residuals'][j], 'whole retained old residual')
    need(len({v['name'] for v in guarded['variables']}) == len(guarded['variables']), 'fresh names')
    plan = dict(schema='fused_nine_factor_literal_source_map_v1', parent_manifest_sha256=PARENT_SEAL,
                ordinary_manifest_sha256=ORDINARY_SEAL,
                old_body_to_new=[[i, i] for i in range(406)],
                old_guarded_to_new=[[i, vm[i]] for i in sorted(vm)],
                old_row_to_new=[dict(old_row=i, new_row=rm.get(i), status='replaced_old_graph' if i in dropped_rows else 'identical')
                                for i in range(len(old['residuals']))],
                removed_parent_graphs=removed, removed_private_coordinates=dropped_aux,
                complete_removed_private_occurrences=occurrences,
                retained_parent_graphs=copy.deepcopy(interface['retained_parent_graphs']), new_fused_graph=mixed,
                all15_signed_targets=copy.deepcopy(interface['all15_signed_targets']),
                all18_actual_power_requests=copy.deepcopy(interface['all18_actual_power_requests']),
                all37_frame_atoms=copy.deepcopy(interface['all37_frame_atoms']),
                helper_reflection=copy.deepcopy(interface['helper_reflection']),
                chronology=copy.deepcopy(interface['chronology']),
                whole_parent_body_pointwise_fixed=True, h_and_signed_A_C_fixed=True,
                other_retained_witness_values_preserved=True, helper_normalization_only_temporary=True,
                BOTH_old_graph_triples_freshly_rechosen=True, new_triple_reused_as_old_strict_triple=False,
                sign_or_power_premise_for_N_or_K_used=False, extra_product_gate_added=False,
                optimizer_projection_or_quartic_executed=False, projected_frontier_claim=False)
    artifacts = {'source.json': source, 'guarded.json': guarded,
                 'domain.json': dict(schema='fused_nine_factor_guard_domain_v1', guards=guards), 'TRANSFORM.json': plan}
    artifacts['CALIBRATION_BINDING.json'] = dict(
        schema='fused_nine_factor_complete_source_calibration_v1', parent_manifest_sha256=PARENT_SEAL,
        ordinary_manifest_sha256=ORDINARY_SEAL, parent_calibration_sha256=digest(PARENT / 'CALIBRATION_BINDING.json'),
        source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
        generated_source_files={n: hashlib.sha256(encoded(v)).hexdigest() for n, v in artifacts.items()},
        formal_native_contracts=read(PARENT / 'CALIBRATION_BINDING.json')['formal_native_contracts'],
        witness_maps=copy.deepcopy(interface['witness_maps']),
        calibration_order=['signed_cap_t_bootstrap', 'positive_Qy_and_Qx_anchors', 'successor_factor_signs',
                           'strict_mixed_product', 'restore_BOTH_old_triples_on_original_body', 'complete_parent_calibration'],
        whole_parent_body_pointwise_fixed=True, other_retained_witness_values_preserved=True,
        complete_parent_guarded_tuple_restored_before_calibration=True,
        new_unbounded_or_Lean_theorem_claimed=False, optimizer_projection_or_quartic_executed=False)
    return artifacts


def protected(path):
    return any(path.resolve().is_relative_to((ROOT / n).resolve())
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
            need(target.read_bytes() == data, 'pure deterministic check ' + name)
        else:
            need(not (HERE / 'MANIFEST.json').exists(), 'sealed packet is immutable')
            need(not target.is_symlink() and (not target.exists() or target.read_bytes() == data), 'refuse changed source')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), pure_check=args.check,
                  source_only=True, source_pins_sha256=digest(HERE / 'SOURCE_PINS.json'),
                  generated={n: hashlib.sha256(encoded(v)).hexdigest() for n, v in artifacts.items()},
                  optimizer_projection_or_quartic_executed=False)
    data = encoded(result)
    need(not args.output.is_symlink() and (not args.output.exists() or args.output.read_bytes() == data), 'refuse changed receipt')
    need(not (HERE / 'MANIFEST.json').exists() or not args.output.resolve().is_relative_to(HERE), 'receipt outside sealed packet')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()
