#!/usr/bin/env python3
"""Fresh static reviewer: no source-array values or predecessor code executed."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
BASE = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS = {
    'residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421',
    'residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
    'residue_affine_packed_history.py': 'd06d17f4464d4c6a21fd0b7dd62a32971d684edbc4786bda062a6f58ce93fcf4',
    'native_binary_index_coupled_units.md': 'efea1218eb5fadc1ad224a2ef6864fb5ea4fecbd5231d7b1379e3e376af690b5',
    'native_controller_boolean_pairs56.md': 'b21d2b985829ee16d09524d96ad36d940bac373f5e98770c119211641703e82e',
}
AUTHOR_PINS = {
    'residue_affine_binary_lane128_tesla.md':'b5d93830a38426f5ac4129d04888efa94b0086932277b969dd810bff0ad1120c',
    'residue_affine_binary_lane128_tesla.py':'14f0119560751ca783faceeff0b0bc35d8f095deeaf528641883794c0f7f8823',
    'residue_affine_binary_lane128_tesla.json':'daa90bb7113164e564444eaca6de7025edaddd0e27fde02f93c9e7b11f4d41ea',
}
LEAVES = ['edge0_hat', 'edge1_hat', 'global_slack', 'height_slack', 'input',
          'native__F0', 'native__F1', 'native__F2', 'native__bound_beta',
          'native__eta', 'native__f', 'native__ga', 'native__h', 'native__i',
          'native__j', 'native__o', 'native__odd_half', 'native__tau_gap',
          'native__y_aux', 'native__zeta', 'product0_hat', 'quotient_hat', 'target']
REMOVED = {'joined_H_sum_30', 'joined_H_shift_31', 'joined_M_shift_38',
           'joined_M_sum_39', 'joined_Z_sum_42', 'joined_Z_shift_43'}
REPLACEMENTS = {
    'joined_H_sum_32': ['joined_H_sum_32', '+', 'edge_0', 'joined_H_shift_29'],
    'native__scaled_B': ['native__scaled_B', '*', 16, 'joined_M_sum_37'],
    'joined_Z_sum_44': ['joined_Z_sum_44', '+', 'edge_0', 'joined_Z_shift_41'],
    'scale_power_46': ['scale_power_46', '*', 'scale_power_45', 'scale_10'],
}

def ck(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def analyze(rows, output='norm_output'):
    definitions = {}
    available = set(LEAVES)
    degrees = {k: 1 for k in LEAVES}
    naive = dict(degrees)
    def deg(x, table):
        return 0 if isinstance(x, int) else table[x]
    for name, op, left, right in rows:
        ck(name not in available, 'duplicate output')
        ck(op in ('+', '-', '*'), 'unexpected operation')
        ck(all(isinstance(x, int) or x in available for x in (left, right)), 'forward/unbound operand')
        degrees[name] = deg(left, degrees) + deg(right, degrees) if op == '*' else max(deg(left, degrees), deg(right, degrees))
        naive[name] = deg(left, naive) + deg(right, naive) if op == '*' else max(deg(left, naive), deg(right, naive))
        definitions[name] = [name, op, left, right]
        available.add(name)
        if name == 'native__R15':
            # Guard every literal premise of (X+ac+gH)^2-(a^2+H)c^2.
            guard = {
                'native__cam2': ['native__cam2', '*', 'native__R10a', 'native__R12'],
                'native__gam': ['native__gam', '*', 'native__ga', 'native__a4m5'],
                'native__D1': ['native__D1', '+', 'native__wn2', 'native__cam2'],
                'native__R14': ['native__R14', '+', 'native__D1', 'native__gam'],
                'native__L15': ['native__L15', '*', 'native__R14', 'native__R14'],
                'native__a_square': ['native__a_square', '*', 'native__R12', 'native__R12'],
                'native__A': ['native__A', '+', 'native__a_square', 'native__a4m5'],
                'native__c2': ['native__c2', '*', 'native__R10a', 'native__R10a'],
                'native__Ac2': ['native__Ac2', '*', 'native__A', 'native__c2'],
                'native__R15': ['native__R15', '-', 'native__L15', 'native__Ac2'],
            }
            ck(all(definitions.get(k) == v for k, v in guard.items()), 'main-norm cancellation guard')
            x,a,c,g,h = [degrees[k] for k in ('native__wn2','native__R12','native__R10a','native__ga','native__a4m5')]
            # Six exact terms: X²,2Xac,2XgH,2acgH,g²H²,-Hc².
            degrees[name] = max(2*x, x+a+c, x+g+h, a+c+g+h, 2*g+2*h, h+2*c)
    live = set()
    stack = [output]
    while stack:
        name = stack.pop()
        if isinstance(name, int) or name in live:
            continue
        live.add(name)
        if name in definitions:
            stack.extend(definitions[name][2:])
    ck(live == available, 'dead row or supplied port')
    factors = ['native__R15','native__P17','native__first_unit','native__bs_q',
               'native__f_square_minus_one','native__index_unit','native__linear_unit']
    residuals = ['norm_residual0','norm_residual1','norm_residual2','norm_residual3']
    return {'M':sum(r[1]=='*' for r in rows), 'A':sum(r[1]!='*' for r in rows),
            'total':len(rows), 'supplied_ports':len(LEAVES), 'positive_witnesses':len(LEAVES)-2,
            'all_rows_and_ports_live':True, 'topological':True,
            'factor_degree_bounds':{k:degrees[k] for k in factors},
            'residual_degree_bounds':{k:degrees[k] for k in residuals},
            'degree_bound':degrees[output], 'naive_degree_bound':naive[output]}

def build():
    deps = []
    for name, expected in PINS.items():
        data = (BASE/name).read_bytes()
        ck(sha(data) == expected, 'dependency pin: '+name)
        deps.append({'path':str((BASE/name).relative_to(ROOT)), 'bytes':len(data), 'sha256':expected,
                     'read_scope':'hash only, no import/execution' if name.endswith('.py') else 'inert full source/proof read'})
    parent = json.loads((BASE/'residue_affine_packed_history.json').read_text())
    before = json.dumps(parent, sort_keys=True, separators=(',',':'))
    old = parent['source']
    child = [list(REPLACEMENTS.get(r[0], r)) for r in old if r[0] not in REMOVED]
    control = [list((REPLACEMENTS.get(r[0], r) if r[0]!='scale_power_46' else r))
               for r in old if r[0] not in REMOVED]
    empty = [list(r) for r in child] + [
        ['empty_endpoint_difference','-','input','target'],
        ['empty_output','*','norm_output','empty_endpoint_difference']]
    old_a = analyze(old)
    new_a = analyze(child)
    ck((old_a['M'],old_a['A'],old_a['degree_bound'])==(64,70,748),'parent ledger/degree')
    ck((new_a['M'],new_a['A'],new_a['degree_bound'])==(61,67,586),'child ledger/degree')
    ck(len([r for r in old if r[0] in REMOVED])==6,'six deletions')
    ck(sum(r[1]=='*' for r in old if r[0] in REMOVED)==3,'three removed products')
    od={r[0]:r for r in old}
    ck(sum(r==od[r[0]] for r in child)==124,'retained literal rows')
    ck(sum(r==od[r[0]] for r in control)==125,'control literal retained rows')
    arrays={'power3':child,'power4':control,'power3_empty':empty}
    reports={name:analyze(rows,'empty_output' if name.endswith('empty') else 'norm_output')
             for name,rows in arrays.items()}
    ck(reports['power4']['degree_bound']==722,'control degree')
    ck((reports['power3_empty']['total'],reports['power3_empty']['M'],reports['power3_empty']['A'],
        reports['power3_empty']['degree_bound'])==(130,62,68,587),'empty option')
    ck(len(AUTHOR_PINS)==3,'author is not yet frozen/pinned')
    author_files=[]
    for name,expected in AUTHOR_PINS.items():
        data=(Path('/tmp')/name).read_bytes()
        ck(sha(data)==expected,'author pin '+name)
        author_files.append({'path':name,'bytes':len(data),'sha256':expected})
    author=json.loads(Path('/tmp/residue_affine_binary_lane128_tesla.json').read_text())
    ck(author['author_helper_sha256']==AUTHOR_PINS['residue_affine_binary_lane128_tesla.py'],
       'author receipt helper binding')
    ck(author['external_positive_inputs']==['input','target'],'ordinary interface')
    ck(set(author['outer_positive_witnesses']+author['native_positive_witnesses'])==set(LEAVES)-{'input','target'},
       'complete witness interface')
    ck(author['fixed_table']==[[3,2],[1,1]],'fixed map')
    ck(set(author['variants'])==set(arrays),'variant coverage')
    for name,rows in arrays.items():
        saved=author['variants'][name]
        ck(saved['source']==rows,'whole independent source reconstruction '+name)
        ledger=saved['ledger']; actual=reports[name]
        ck((ledger['operations'],ledger['multiplications'],ledger['additions_subtractions'],
            ledger['positive_witnesses'],ledger['supplied_ports'])==
           (actual['total'],actual['M'],actual['A'],actual['positive_witnesses'],actual['supplied_ports']),
           'full ledger '+name)
        ck(ledger['canonical_rows_sha256']==sha(json.dumps(rows,separators=(',',':')).encode()),'array digest')
        ck(saved['manual_degree_upper_bound']==actual['degree_bound'],'manual bound '+name)
        if name!='power3_empty':
            ck(saved['certificate']=={'operations':114,'multiplications':56,
                                      'additions_subtractions':58,'comparisons':5},'certificate')
            ck(rows[49:]==old[55:],'literal native/finalizer tail')
        for port,consumers in {'native__F0':['native__shared_sum02','native__bs_packed'],
                               'native__bound_beta':['native__bs_X_bound']}.items():
            ck([r[0] for r in rows if port in r[2:]]==consumers,'private native consumers')
    for item in author['dependencies']:
        data=(ROOT/item['path']).read_bytes()
        ck(sha(data)==item['sha256'] and len(data)==item['bytes'] and len(data.splitlines())==item['lines'],
           'author dependency binding')
    ck(json.dumps(parent,sort_keys=True,separators=(',',':'))==before,'parent mutation')
    return {'status':'PASS_INDEPENDENT_STATIC_SOURCE_AND_DEGREE','dependencies':deps,'author_files':author_files,
            'parent':old_a,'variants':reports,'source_rows_checked':sum(len(x) for x in arrays.values()),
            'removed':sorted(REMOVED),'replacements':REPLACEMENTS,'independently_reconstructed_sources':arrays,
            'execution_limits':{'source_array_values_evaluated':False,'degree_propagation_only':True,
                                'predecessor_or_author_code_imported_or_executed':False,
                                'native_soundness_inherited_not_reproved':True,'repository_mutation':False},
            'helper_sha256':sha(Path(__file__).read_bytes())}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    parser.add_argument('--expect',type=Path)
    args=parser.parse_args()
    report=build()
    if args.output:
        args.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    if args.expect:
        ck(json.dumps(json.loads(args.expect.read_text()),sort_keys=True)==json.dumps(report,sort_keys=True),'receipt mismatch')
    print('PASS: independent386-row reconstruction, full liveness, degrees586/722/587; no array evaluation')

if __name__=='__main__':
    main()
