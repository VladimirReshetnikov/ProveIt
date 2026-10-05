"""Original metadata-only splice of an independently proved arithmetic cut.

No source, polynomial, coefficient or degree evaluation. Read literal rows,
replace a named cut, and check topology/counts/bindings. Freeze after first run.
"""
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT = BASE / 'positive7_complete_sparse_compiler_root.json'
PARENT_PIN = '2c7e2b2d2345150644b47701eed9434eabad7159f0067154b6666750e2b48e3a'


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read_pinned(path, pin):
    raw = path.read_bytes()
    if digest(raw) != pin:
        raise ValueError('changed input ' + str(path))
    return json.loads(raw), {'path': str(path), 'sha256': pin, 'bytes': len(raw)}


def census(rows):
    bins = Counter(row[1] for row in rows)
    return {'M': bins['*'], 'A': bins['+']+bins['-'], 'operations': len(rows)}


def compact_pin(rows):
    return digest(json.dumps(rows, separators=(',', ':')).encode())


def inspect_graph(rows, supplied, output):
    defined = set(supplied)
    if len(defined) != len(supplied):
        raise ValueError('duplicate supplied symbol')
    operands = {}
    roles = set()
    for name, op, left, right in rows:
        if name in defined or op not in ('+', '-', '*'):
            raise ValueError('invalid source row')
        for field in (left, right):
            if isinstance(field, str):
                if field not in defined:
                    raise ValueError('undefined operand ' + field)
            elif isinstance(field, dict):
                if set(field) != {'fixed'}:
                    raise ValueError('bad fixed role')
                roles.add(field['fixed'])
            elif not isinstance(field, int):
                raise ValueError('bad literal')
        defined.add(name)
        operands[name] = (left, right)
    live = set()
    pending = [output]
    while pending:
        value = pending.pop()
        if isinstance(value, str) and value not in live:
            live.add(value)
            pending.extend(operands.get(value, ()))
    if set(operands)-live or set(supplied)-live:
        raise ValueError('dead rows or supplied symbols')
    return {'all_rows_live': True, 'all_supplied_live': True,
            'topologically_closed': True, 'named_fixed_roles': sorted(roles)}


def compose_graph(parent, local_rows, local_outputs):
    old = parent['source']
    start = next(i for i, row in enumerate(old) if row[0].startswith('paired_term_'))
    end = next(i for i, row in enumerate(old) if row[0] == 'five_increment_sum_1')
    removed = old[start:end]
    if any(not row[0].startswith(('paired_term_', 'relator_term_', 'increment_')) for row in removed):
        raise ValueError('wrong cut contents')
    if census(removed) != {'M': 174+24*parent['r'], 'A': 168+24*parent['r'],
                           'operations':342+48*parent['r']}:
        raise ValueError('parent increment census changed')
    replacement = list(local_rows)
    outputs = list(local_outputs)
    relator_rows = [row for row in removed if row[0].startswith('relator_term_')]
    for coordinate in range(3,6):
        matches = [row for row in relator_rows if row[0].startswith('relator_term_'+str(coordinate)+'_')]
        if len(matches) != 8*parent['r']:
            raise ValueError('relator row partition')
        for index, row in enumerate(matches):
            replacement.append(row)
            name = 'paired_relator_sum_'+str(coordinate)+'_'+str(index)
            replacement.append([name, '+', outputs[coordinate], row[0]])
            outputs[coordinate] = name
    replacement_counts = census(replacement)
    wanted = {'M':30+24*parent['r'], 'A':168+24*parent['r'],
              'operations':198+48*parent['r']}
    if replacement_counts != wanted:
        raise ValueError('new increment census')
    binding = dict(zip(parent['ports']['six_increments'], outputs))

    def rename(field):
        return binding.get(field, field) if isinstance(field, str) else field

    suffix = [[name, op, rename(a), rename(b)] for name,op,a,b in old[end:]]
    rows = old[:start]+replacement+suffix
    result = dict(parent)
    result['source'] = rows
    result['ports'] = dict(parent['ports'], six_increments=outputs)
    result['certificate_prefix_rows'] = parent['certificate_prefix_rows']-144
    result['certificate_ledger'] = census(rows[:result['certificate_prefix_rows']])
    result['polynomial_ledger'] = census(rows)
    result['stages'] = dict(parent['stages'])
    result['stages']['sparse_increment_rows'] = replacement_counts
    result.pop('paired_coefficient_occurrences')
    result['static_checks'] = inspect_graph(rows, parent['ordinary_parameters']+parent['positive_auxiliaries'], parent['output'])
    if result['certificate_ledger'] != {'M':parent['certificate_ledger']['M']-144,
                                        'A':parent['certificate_ledger']['A'],
                                        'operations':parent['certificate_ledger']['operations']-144}:
        raise ValueError('certificate delta')
    if result['static_checks'] != parent['static_checks']:
        raise ValueError('changed fixed roles or graph status')
    result['substitution'] = {
        'parent_source_sha256_compact':compact_pin(old),
        'new_source_sha256_compact':compact_pin(rows),
        'old_cut_first_index':start, 'old_cut_end_index_exclusive':end,
        'old_cut_census':census(removed), 'new_cut_census':replacement_counts,
        'six_boundary_bindings':binding,
        'outside_prefix_identical':rows[:start] == old[:start],
        'outside_suffix_only_boundary_renamed':rows[start+len(replacement):] == suffix,
        'relator_products_preserved_literally':len(relator_rows),
        'positive_coordinates_comparisons_lanes_and_native_block_unchanged':True,
        'source_arithmetic_evaluated':False,
    }
    return result


def main():
    # Local normalized graph schema is a separate inert JSON data file.
    local_path, local_pin = Path(sys.argv[1]), sys.argv[2]
    local, local_input = read_pinned(local_path, local_pin)
    parent, parent_input = read_pinned(PARENT, PARENT_PIN)
    local_rows, local_outputs = local['source'], local['outputs']
    if len(local_outputs) != 6 or census(local_rows) != {'M':30,'A':168,'operations':198}:
        raise ValueError('wrong local cut shape')
    expected_ports = [[2,3,4,5,6,7]]*2+[[1,2,3,4,5,7]]*2+[list(range(1,8))]*4
    expected_names = ['selected_'+str(slot)+'_'+str(port)
                      for slot, ports in enumerate(expected_ports) for port in ports]
    if local['supplied'] != expected_names:
        raise ValueError('wrong local supplied port order')
    examples = [compose_graph(graph, local_rows, local_outputs) for graph in parent['examples']]
    shapes = []
    for old in parent['static_shape_censuses']:
        new = dict(old)
        for key in ('certificate_ledger','polynomial_ledger'):
            new[key] = {'M':old[key]['M']-144,'A':old[key]['A'],
                        'operations':old[key]['operations']-144}
        shapes.append(new)
    receipt = {
        'status':'original metadata-only complete cut composition PASS',
        'emitter_sha256':digest(Path(__file__).read_bytes()),
        'inputs':[parent_input,local_input],
        'generic_ledger':{'certificate':'(276+56r+lambda)M+(550+74r)A',
                          'single_polynomial':'(299+56r+lambda)M+(595+74r)A',
                          'polynomial_operations':'894+130r+lambda(62+10r)',
                          'positive_witnesses':'96+10r','comparisons':23,
                          'lambda':'floor(log2 ell)+popcount(ell)-1',
                          'saving':'144M, zero A, exactly144 total'},
        'fixed_data_recipe':parent['fixed_data_recipe'],
        'static_shape_censuses':shapes,
        'count_only_scope':'r=2,3,8 use inherited count metadata and the proved constant cut delta; full new arrays saved only for r=0,1,4',
        'examples':examples,
        'execution_scope':{'metadata_only':True,'arithmetic_evaluation':False,
                           'degree_propagation':False,'frozen_helper_execution':False,
                           'numerical_universal_relator_list_supplied':False},
    }
    path = Path('/tmp/positive7_inverse_pair_compose_root.json')
    if path.exists():
        raise ValueError('refuse overwrite')
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'receipt_sha256':digest(path.read_bytes()),
                      'rows':sum(len(g['source']) for g in examples),
                      'shape_ledgers':shapes},indent=2))


if __name__ == '__main__':
    main()
