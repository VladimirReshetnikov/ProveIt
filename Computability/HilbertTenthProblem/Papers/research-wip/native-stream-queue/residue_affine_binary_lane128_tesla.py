#!/usr/bin/env python3
"""Fresh static 134->128 emitter and handwritten outer-word diagnostics.

No predecessor module is imported and no parent/child source array is evaluated.
The only source-array operations are inert editing, equality, dependency closure,
consumer guards, counts and byte hashes. Degree entries are a manual proof ledger.
Finite handwritten word checks do not construct native Pell zeros.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP = Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS = {
 'residue_affine_packed_history.json': 'b2865672ed7cf629aba52e0b528b358670b8faf857b5e0a9a819b7e3c09c7421',
 'residue_affine_packed_history.md': '0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882',
 'native_binary_index_coupled_units.md': 'efea1218eb5fadc1ad224a2ef6864fb5ea4fecbd5231d7b1379e3e376af690b5',
 'native_controller_boolean_pairs56.md': 'b21d2b985829ee16d09524d96ad36d940bac373f5e98770c119211641703e82e',
}
DELETED = [
 ['joined_H_sum_30', '+', 'edge_1', 'joined_H_shift_29'],
 ['joined_H_shift_31', '*', 'scale_10', 'joined_H_sum_30'],
 ['joined_M_shift_38', '*', 'scale_10', 'joined_M_sum_37'],
 ['joined_M_sum_39', '+', 'selector_sum_2', 'joined_M_shift_38'],
 ['joined_Z_sum_42', '+', 'edge_1', 'joined_Z_shift_41'],
 ['joined_Z_shift_43', '*', 'scale_10', 'joined_Z_sum_42'],
]
EDITS = {
 'joined_H_sum_32': ['joined_H_sum_32', '+', 'edge_0', 'joined_H_shift_29'],
 'native__scaled_B': ['native__scaled_B', '*', 16, 'joined_M_sum_37'],
 'joined_Z_sum_44': ['joined_Z_sum_44', '+', 'edge_0', 'joined_Z_shift_41'],
}
OUTER = ['edge0_hat','edge1_hat','quotient_hat','product0_hat','height_slack','global_slack']
NATIVE = ['native__'+s for s in ['F0','F1','F2','odd_half','bound_beta','eta','zeta','f','o','y_aux','h','ga','i','j','tau_gap']]
FREE = set(['input','target'] + OUTER + NATIVE)

def need(test, message):
    if not test:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def row_hash(rows):
    return digest(json.dumps(rows, separators=(',', ':')).encode())

def structural(rows, output):
    known = set(FREE)
    producers = {}
    for row in rows:
        need(len(row) == 4, 'row arity')
        name, op, left, right = row
        need(name not in known and op in ['+','-','*'], 'unique producer/operator')
        need(all(isinstance(t,int) or t in known for t in [left,right]), 'topology')
        producers[name] = row
        known.add(name)
    pending = [output]
    live = set()
    while pending:
        name = pending.pop()
        if name in live:
            continue
        live.add(name)
        if name in producers:
            pending.extend(t for t in producers[name][2:] if isinstance(t,str))
    need(set(producers) <= live, 'dead producer')
    need(live & FREE == FREE, 'missing free port')
    return {'operations':len(rows), 'multiplications':sum(r[1]=='*' for r in rows),
            'additions_subtractions':sum(r[1]!='*' for r in rows),
            'supplied_ports':len(FREE), 'positive_witnesses':21,
            'all_rows_live':True, 'all_ports_live':True, 'output':output,
            'canonical_rows_sha256':row_hash(rows)}

def emit(parent, exponent):
    by_name = {r[0]:r for r in parent}
    need(len(parent)==134 and len(by_name)==134, 'parent size')
    for row in DELETED:
        need(by_name.get(row[0]) == row, 'deleted row binding')
    expected_old = {
       'joined_H_sum_32':['joined_H_sum_32','+','edge_0','joined_H_shift_31'],
       'native__scaled_B':['native__scaled_B','*',16,'joined_M_sum_39'],
       'joined_Z_sum_44':['joined_Z_sum_44','+','edge_0','joined_Z_shift_43'],
       'scale_power_46':['scale_power_46','*','scale_power_45','scale_power_45'],
    }
    for name,row in expected_old.items():
        need(by_name.get(name)==row, 'edit input binding')
    deleted_names = {r[0] for r in DELETED}
    edits = dict(EDITS)
    if exponent == 3:
        edits['scale_power_46'] = ['scale_power_46','*','scale_power_45','scale_10']
    child = [list(edits.get(r[0],r)) for r in parent if r[0] not in deleted_names]
    # Every native producer after input padding, and the entire finalizer, is literal.
    need(child[49:] == parent[55:], 'retained native/finalizer block')
    need([r for r in child if r[0] in ['native__bs_packed','native__bs_X_bound']] ==
         [r for r in parent if r[0] in ['native__bs_packed','native__bs_X_bound']], 'private restoration rows')
    for port, consumers in {
       'native__F0':['native__shared_sum02','native__bs_packed'],
       'native__bound_beta':['native__bs_X_bound'],
    }.items():
        need([r[0] for r in child if port in r[2:]]==consumers, 'private consumer guard')
    need(all(not (set(r[2:]) & set(NATIVE)) for r in child[:49]), 'outer independence')
    return child, {'deleted_rows':DELETED, 'edited_rows':[
        {'before':by_name[name],'after':row} for name,row in edits.items()],
        'literal_retained_rows':sum(r==by_name[r[0]] for r in child),
        'retained_tail_rows':len(parent[55:]), 'private_consumer_guards':True}

def complement_checks():
    pairs = subsets = 0
    for J in range(256):
        for E0 in range(J+1):
            E1 = J-E0
            original = ((E0 & J)==E0 and (E1 & J)==E1)
            shortened = (E0 & J)==E0
            need(original==shortened, 'binary complement equivalence')
            if shortened:
                need((E0 & E1)==0 and (E0 | E1)==J, 'disjoint complement')
                subsets += 1
            pairs += 1
    # A third summand invalidates the unrestricted last-selector deletion.
    need(1+1+3==5 and (1&5)==1 and (3&5)!=3, 'three-selector boundary')
    return {'J_inclusive':[0,255], 'pairs':pairs, 'subset_pairs':subsets,
            'three_selector_counterexample':{'J':5,'selectors':[1,1,3]}}

def lane_checks():
    count = accepted = 0
    h = 4
    B = 8*h
    for T in [1,2]:
        P = B**T
        J = (P-1)//(B-1)
        for e in range(J+1):
            e1 = J-e
            for w in range(J+1):
                for z in range(J+1):
                    m = (B-1)*e
                    rg = (h-1)*J
                    H3 = e+P*w+P*P*w
                    M3 = J+P*m+P*P*rg
                    A3 = e+P*z+P*P*w
                    H4 = e+P*e1+P*P*w+P**3*w
                    M4 = J+P*J+P*P*m+P**3*rg
                    A4 = e+P*e1+P*P*z+P**3*w
                    new = (H3&M3)==A3
                    old = (H4&M4)==A4
                    scalar = ((e&J)==e and (w&m)==z and (w&rg)==w)
                    need(new==old==scalar, 'three/four lane comparison')
                    need(max(H3,M3,A3)<P**3<B*P**3, 'short pack bound')
                    count += 1
                    accepted += new
    return {'synthetic_B':B,'synthetic_h':h,'T_values':[1,2],
            'bounded_assignments':count,'accepted_lane_assignments':accepted,
            'scope':'Handwritten scalar words; not source arrays or native zeros.'}

def path_checks():
    cases = zero_words = corruptions = 0
    for x in range(1,25):
        for T in range(1,7):
            states = [x]
            for _ in range(T):
                v = states[-1]
                states.append((3*v+1)//2 if v%2 else v//2)
            target = states[-1]
            quotients = [(v-1)//2 for v in states[:-1]]
            h = 1
            while h <= max(x+target, max(quotients)):
                h *= 2
            B = 8*h
            P = B**T
            J = (P-1)//(B-1)
            E0 = sum((v%2)*B**j for j,v in enumerate(states[:-1]))
            E1 = J-E0
            W = sum(v*B**j for j,v in enumerate(quotients))
            Z = sum((states[j]%2)*v*B**j for j,v in enumerate(quotients))
            beta = P-J-(W+1)-(Z+1)
            need(beta>0 and h-x-target>0, 'positive outer slack')
            N = W+2*Z+J+E0
            C = 2*W+J+E1
            need(B*N+x==C+P*target, 'chronological equality')
            need((E0&J)==E0 and (E1&J)==E1, 'typed selectors')
            need((W&((B-1)*E0))==Z and (W&((h-1)*J))==W, 'selected/range words')
            H = E0+P*W+P*P*W
            M = J+P*(B-1)*E0+P*P*(h-1)*J
            A = E0+P*Z+P*P*W
            need((H&M)==A and max(H,M,A)<P**3<B*P**3, 'path pack')
            need(B*N+x != C+P*(target+1), 'wrong endpoint rejection')
            need((W&((B-1)*E0)) != Z+1, 'selected-product corruption')
            cases += 1
            zero_words += W==0
            corruptions += 2
    return {'starting_inputs_inclusive':[1,24], 'horizons_inclusive':[1,6],
            'genuine_histories':cases, 'zero_quotient_histories':zero_words,
            'single_port_rejections':corruptions,
            'scope':'Fresh direct Collatz paths and handwritten outer formulas only; no native Pell tuples.'}

def build():
    deps=[]
    for name,sha in PINS.items():
        b=(ROOT/WIP/name).read_bytes()
        need(digest(b)==sha, 'dependency pin '+name)
        deps.append({'path':str(WIP/name),'sha256':sha,'bytes':len(b),'lines':len(b.splitlines())})
    parent=json.loads((ROOT/WIP/'residue_affine_packed_history.json').read_text())
    need(parent['default_table']==[[3,2],[1,1]], 'fixed table')
    old=parent['source']
    need(structural(old,'norm_output')['multiplications']==64, 'parent ledger')
    arrays={}
    for exponent in [3,4]:
        rows,delta=emit(old,exponent)
        stats=structural(rows,'norm_output')
        need(stats['operations']==128 and stats['multiplications']==61, 'child ledger')
        arrays['power'+str(exponent)]={'source':rows,'ledger':stats,'delta':delta,
            'certificate':{'operations':114,'multiplications':56,'additions_subtractions':58,'comparisons':5},
            'manual_degree_upper_bound':586 if exponent==3 else 722}
    rows=arrays['power3']['source']+[
       ['empty_endpoint_difference','-','input','target'],
       ['empty_output','*','norm_output','empty_endpoint_difference']]
    arrays['power3_empty']={'source':rows,'ledger':structural(rows,'empty_output'),
                           'manual_degree_upper_bound':587}
    need(arrays['power3_empty']['ledger']['multiplications']==62, 'empty count')
    return {'status':'PASS','scope':'Static source emission only; no numeric or symbolic source-array evaluation.',
       'author_helper_sha256':digest(Path(__file__).read_bytes()), 'dependencies':deps,
       'external_positive_inputs':['input','target'], 'outer_positive_witnesses':OUTER,
       'native_positive_witnesses':NATIVE,'fixed_table':[[3,2],[1,1]],'variants':arrays,
       'manual_degree_ledger':{
          'power3':{'factor_bounds':[92,220,51,7,120,42,42],'residual_bounds':[2,3,5,6],'total':586},
          'power4':{'factor_bounds':[114,272,63,9,148,52,52],'residual_bounds':[2,3,5,6],'total':722},
          'parent':{'factor_bounds':[118,280,65,9,152,54,54],'residual_max':8,'total':748},
          'scope':'Constants transcribed from the handwritten proof, not source-array degree propagation.'},
       'complement_checks':complement_checks(),'lane_checks':lane_checks(),'path_checks':path_checks(),
       'non_dyadic_factor_boundary':{'B':24,'P':2048,'J':89,'identity':(24-1)*89+1==2048}}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--receipt',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    result=build()
    encoded=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.write:
        args.receipt.write_text(encoded)
    else:
        need(args.receipt.read_text()==encoded, 'receipt differs')
    print('PASS: three static arrays / 386 rows; 128=61M+67A, 21 witnesses; no source-array evaluation')

if __name__=='__main__':
    main()
