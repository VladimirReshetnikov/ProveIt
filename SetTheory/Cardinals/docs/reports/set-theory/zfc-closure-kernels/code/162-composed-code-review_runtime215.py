#!/usr/bin/env python3
"""Independent interface/inventory audit of the final K215 runtime evidence.

This does not rerun the symbolic proof or treat per-case summaries as a kernel
proof. It checks their complete inventory, positive-duration metadata, literal
row coverage, content bindings, and the address/ordinal interface separately.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

SOURCE_SHA = '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
TABLE_SHA = '03739f080d023166773bc14e7e3a4d8157f81d44c28cd30fef46066b37cf3748'
CASES_SHA = 'c81f74348618cf7ffa0fea898f044ce71b7c1f2aff5e5ef04118c33b7333c2c5'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def successor(code):
    # Binary increment by carry propagation, independently of runtime.inc.
    out = list(code)
    for i in range(len(out)-1, -1, -1):
        if out[i] == '0':
            out[i] = '1'
            return ''.join(out), 0
        out[i] = '0'
    return ''.join(out), 1

def truncate(code, side, rank):
    marks = [i for i, bit in enumerate(code) if bit == side]
    return code[:marks[-rank]] if len(marks) >= rank else ''

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    root = args.packet
    source_path = root/'source/sites215.json'
    table_path = root/'machine/k215.native.tm'
    cases_path = root/'evidence/runtime_cases.json.gz'
    receipt_path = root/'evidence/runtime.json'
    need(sha(source_path) == SOURCE_SHA, 'Unexpected source bytes')
    need(sha(table_path) == TABLE_SHA, 'Unexpected table bytes')
    need(sha(cases_path) == CASES_SHA, 'Unexpected case receipt bytes')
    source = json.loads(source_path.read_text())
    receipt = json.loads(receipt_path.read_text())
    with gzip.open(cases_path, 'rt') as handle:
        cases = json.load(handle)
    need(receipt['table_sha256'] == TABLE_SHA, 'Receipt table binding')
    need(receipt['source_sha256'] == SOURCE_SHA, 'Receipt source binding')
    need(receipt['case_receipts_sha256'] == CASES_SHA, 'Receipt case binding')
    for key, rel in [('checker_sha256','code/runtime/symbolic_runtime.py'),
                     ('helper_sha256','code/runtime/independent_runtime.py'),
                     ('wrapper_sha256','code/validate_runtime.py')]:
        need(receipt[key] == sha(root/rel), 'Checker binding: '+key)

    # Build the full prefix tree without importing source_compare or runtime.
    trie = {}
    for i, (path, op, arg) in enumerate(source):
        node = trie
        need(path and set(path) <= {'0','1'}, 'Invalid address')
        for bit in path:
            need('leaf' not in node, 'Address extends a leaf')
            node = node.setdefault(bit, {})
        need(not node, 'Duplicate or prefix-overlapping address')
        node['leaf'] = i
    intervals = {}
    order = []
    def visit(node, prefix):
        lo = len(order)
        if 'leaf' in node:
            need(set(node) == {'leaf'}, 'Non-leaf terminal')
            order.append(node['leaf'])
        else:
            need(set(node) == {'0','1'}, 'Incomplete binary tree')
            visit(node['0'], prefix+'0')
            visit(node['1'], prefix+'1')
        intervals[prefix] = (lo, len(order))
    visit(trie, '')
    need(order == list(range(len(source))), 'Source is not in tree order')
    def resolve(code):
        need(len(code) <= 64, 'Raw successor too long')
        padded = code.ljust(64, '0')
        node = trie
        depth = 0
        while 'leaf' not in node:
            need(depth < len(padded), 'No dispatch leaf')
            node = node[padded[depth]]
            depth += 1
        need(set(padded[depth:]) <= {'0'}, 'Stray control ones after target leaf')
        return node['leaf']
    need(resolve('') == 0, 'Blank control area must dispatch first leaf')
    expected_cases = []
    checked_edges = overflows = halt_sites = 0
    for i, (path, op, arg) in enumerate(source):
        need(resolve(path) == i, 'Leaf address fails to resolve to itself')
        guards = (False, True) if op == 'CD' else (False,)
        for positive in guards:
            expected_cases.append((i, positive))
            if op == 'CH':
                halt_sites += 1
                continue
            if op == 'CI' or (op == 'CD' and positive):
                raw, overflow = successor(path)
                ordinal = (i+1) % len(source)
            else:
                side = '1' if op == 'CC' else '0'
                rank = arg if op in ('CB','CC') else 1
                cut = truncate(path, side, rank)
                ancestors = [path[:j] for j in range(len(path)-1,-1,-1) if path[j] == side]
                if len(ancestors) < rank:
                    ordinal = 0
                else:
                    lo, hi = intervals[ancestors[rank-1]]
                    ordinal = lo if op == 'CC' else hi % len(source)
                raw, overflow = (cut, 0) if op == 'CC' else successor(cut)
            need(resolve(raw) == ordinal, 'Address/ordinal successor disagreement')
            checked_edges += 1
            overflows += overflow
    need([(c['site_index'],c['positive']) for c in cases] == expected_cases,
         'Incomplete, duplicate, reordered, or extra runtime cases')
    need(all(type(c['positive']) is bool for c in cases), 'Guard types')
    need(len(cases) == 6176 and checked_edges == 6175 and halt_sites == 1,
         'Unexpected inventory')
    total_steps = 0
    kinds = {'literal':0, 'unary':0, 'list':0}
    nonhalt_constants = []
    legacy_rows = set()
    for c in cases:
        duration = c['duration']
        need(len(duration) == 13 and all(type(v) is int and v >= 0 for v in duration),
             'Invalid nonnegative affine duration')
        need(duration[0] > 0, 'Missing strict primitive progress')
        need(0 < c['symbolic_steps'] < 4000, 'Construction fuel metadata')
        need(sum(c['kinds'].values()) == c['symbolic_steps'], 'Step-kind inventory')
        total_steps += c['symbolic_steps']
        for k, v in c['kinds'].items():
            need(k in kinds, 'Unknown symbolic rule')
            kinds[k] += v
        legacy_rows.update(map(tuple,c['rows']))
        if source[c['site_index']][1] != 'CH':
            nonhalt_constants.append(duration[0])
    need(total_steps == receipt['symbolic_steps'] == 1698790, 'Step sum')
    need(receipt['minimum_duration_constant'] == min(c['duration'][0] for c in cases),
         'Minimum duration')
    table = {}
    for line in table_path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,z = line.split()
        row = int(q),int(b)
        need(row not in table, 'Duplicate row')
        table[row] = (int(w),1 if d == 'R' else -1,int(z))
    states = {q for q,b in table}
    mapping = {int(k):int(v) for k,v in json.loads((root/'code/inputs/legacy_mapping.json').read_text()).items()}
    for q in states|{254}:
        mapping.setdefault(q,q+1000)
    need(len({mapping[q] for q in states|{254}}) == len(states)+1, 'Legacy mapping collision')
    need((mapping[0],mapping[84],mapping[254]) == (95,96,254), 'Entry/exit binding')
    inverse = {mapping[q]:q for q in states}
    mapped = {(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in table.items()}
    for block in receipt['blocks']:
        for event in block['trace']:
            if event[0] in ('literal','unary'):
                q,b,w,d,z = event[1]
                need(mapped[q,b] == (w,d,z), 'Block trace row/table mismatch')
                legacy_rows.add((q,b))
    native_rows = {(inverse[q],b) for q,b in legacy_rows}
    need(native_rows == set(table), 'Row inventory coverage')
    result = {
        'status':'INDEPENDENT_INTERFACE_AND_RECEIPT_AUDIT_PASS',
        'source_sha256':SOURCE_SHA,'native_table_sha256':TABLE_SHA,
        'case_receipts_sha256':CASES_SHA,'reviewer_sha256':sha(Path(__file__)),
        'primitive_occurrences':len(source),'guarded_cases':len(cases),
        'nonhalting_successors_checked':checked_edges,'halt_sites':halt_sites,
        'raw_address_equals_ordinal_successor_for_every_guard':True,
        'all_successors_have_only_zero_padding_after_the_resolved_leaf':True,
        'empty_control_area_dispatches_to_ordinal_zero':True,
        'overflow_successors':overflows,
        'symbolic_proof_steps':total_steps,
        'maximum_symbolic_construction_steps_per_case':max(c['symbolic_steps'] for c in cases),
        'minimum_duration_constant':min(c['duration'][0] for c in cases),
        'minimum_nonhalting_duration_constant':min(nonhalt_constants),
        'all_duration_coefficients_nonnegative':True,
        'all_duration_constants_strictly_positive':True,
        'rule_counts':kinds,'covered_transition_rows':len(native_rows),
        'legacy_entry_exit_mapping':[95,96,254],
        'scope':'Independent receipt/interface audit and manual review of rule soundness. This audit does not replay the full symbolic derivations and is not a proof-assistant kernel artifact.'
    }
    encoded = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded,end='')

if __name__ == '__main__':
    main()
