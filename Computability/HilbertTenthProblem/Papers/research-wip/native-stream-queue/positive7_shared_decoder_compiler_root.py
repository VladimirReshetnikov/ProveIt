"""Original one-run inert-record composer; freeze with its first receipt.

No instruction/coefficient evaluation, scientific import, or degree propagation.
"""
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT = BASE / 'positive7_left_scale_compiler_root.json'
OUT = Path('/tmp/positive7_shared_decoder_compiler_root.json')
assert not OUT.exists(), 'First receipt already exists: never replay this composer'
raw = PARENT.read_bytes()
assert sha256(raw).hexdigest() == '9a17d38559ae0fc1aac7c987fab827120cdda346fdf2b85fe1b0eb9b1b523d4a'
parent = json.loads(raw)


def digest(records):
    return sha256(json.dumps(records, separators=(',', ':')).encode()).hexdigest()


def census(records):
    labels = Counter(row[1] for row in records)
    assert set(labels) <= {'*', '+', '-'}
    return {'M': labels['*'], 'A': labels['+'] + labels['-'], 'operations': len(records)}


def static_check(records, graph):
    supplied = set(graph['ordinary_parameters'] + graph['positive_auxiliaries'])
    known = set(supplied)
    definitions = {}
    fixed_uses = Counter()
    for name, op, left, right in records:
        assert name not in known and op in ('*', '+', '-')
        for operand in (left, right):
            if isinstance(operand, str):
                assert operand in known, (name, operand)
            elif isinstance(operand, dict):
                assert set(operand) == {'fixed'} and isinstance(operand['fixed'], str)
                fixed_uses[operand['fixed']] += 1
            else:
                assert type(operand) is int
        definitions[name] = (left, right)
        known.add(name)
    live = {graph['output']}
    for name, _, left, right in reversed(records):
        if name in live:
            live.update(x for x in (left, right) if isinstance(x, str))
    assert set(definitions) <= live and supplied <= live
    assert all(n == 1 for n in fixed_uses.values())
    return {'topology': True, 'all_computed_live': True, 'all_supplied_live': True,
            'named_fixed_roles': sorted(fixed_uses)}


examples = []
expected = {1: (259, 553), 2: (286, 592), 4: (350, 676)}
for old in parent['examples']:
    r = old['r']
    assert r in expected
    pieces = []
    cursor = 0
    cut = None
    for stage, counts in old['stages'].items():
        rows = old['source'][cursor:cursor + counts['operations']]
        cursor += counts['operations']
        assert census(rows) == counts
        if stage == 'shared_centered_input_forms':
            assert cut is None
            cut = rows
            assert census(cut) == {'M': 8*r, 'A': 8*r, 'operations': 16*r}
            decode = [
                ['shared_decode_c1', '-', 'H_4', 'H_7'],
                ['shared_decode_k', '-', 'shared_decode_c1', 'H_7'],
                ['shared_decode_c2', '+', 'shared_decode_k', 'H_5'],
                ['shared_decode_k2', '+', 'shared_decode_k', 'shared_decode_k'],
                ['shared_decode_c3', '+', 'shared_decode_k2', 'H_6'],
            ]
            forms = []
            for j in range(r):
                u1, u2 = f'decoded_u_{j}_1', f'decoded_u_{j}_2'
                v1, v2, v3 = (f'decoded_v_{j}_{i}' for i in (1, 2, 3))
                us, vs, vt = f'decoded_u_sum_{j}', f'decoded_v_pair_{j}', f'decoded_v_sum_{j}'
                forms.extend([
                    [u1, '*', {'fixed': f'form_basis_u_{j}_1'}, 'shared_decode_c1'],
                    [u2, '*', {'fixed': f'form_basis_u_{j}_2'}, 'shared_decode_c2'],
                    [us, '+', u1, u2],
                    [f'centered_form_{j}_1', '+', us, 'center_word'],
                    [v1, '*', {'fixed': f'form_basis_v_{j}_1'}, 'shared_decode_c1'],
                    [v2, '*', {'fixed': f'form_basis_v_{j}_2'}, 'shared_decode_c2'],
                    [v3, '*', {'fixed': f'form_basis_v_{j}_3'}, 'shared_decode_c3'],
                    [vs, '+', v1, v2],
                    [vt, '+', vs, v3],
                    [f'centered_form_{j}_2', '+', vt, 'center_word'],
                ])
            pieces.extend([('shared_history_decoder', decode), ('sparse_centered_input_forms', forms)])
        else:
            pieces.append((stage, rows))
    assert cursor == len(old['source']) and cut is not None
    new = deepcopy(old)
    del new['left_scale_splice']
    new['source'] = [row for _, rows in pieces for row in rows]
    new['stages'] = {stage: census(rows) for stage, rows in pieces}
    new['polynomial_ledger'] = census(new['source'])
    assert (new['polynomial_ledger']['M'], new['polynomial_ledger']['A']) == expected[r]
    assert new['source'][-68:] == old['source'][-68:]
    new['certificate_prefix_rows'] = len(new['source']) - 68
    new['certificate_ledger'] = census(new['source'][:-68])
    new['ports']['decoded_history_fields'] = ['shared_decode_c1', 'shared_decode_c2', 'shared_decode_c3']
    new['static_checks'] = static_check(new['source'], new)
    roles = set(new['static_checks']['named_fixed_roles'])
    old_roles = set(old['static_checks']['named_fixed_roles'])
    retired = {f'form_ell_{j}_{i}_{k}' for j in range(r) for i in (1, 2) for k in (4, 5, 6, 7)}
    introduced = {f'form_basis_{b}_{j}_{i}' for j in range(r) for b, indices in [('u', (1, 2)), ('v', (1, 2, 3))] for i in indices}
    assert roles == (old_roles - retired) | introduced
    assert retired <= old_roles and len(roles) == 6 + 15*r
    exits = {f'centered_form_{j}_{i}' for j in range(r) for i in (1, 2)}
    cut_names = {row[0] for row in cut}
    outside = [row for row in old['source'] if row[0] not in cut_names]
    assert [row for row in new['source'] if row[0] in {x[0] for x in outside}] == outside
    external = {name: [] for name in sorted(exits)}
    for row in outside:
        for index, operand in enumerate(row[2:], 2):
            if isinstance(operand, str) and operand in cut_names:
                assert operand in exits
                external[operand].append({'consumer': row[0], 'operand_index': index})
    assert all(external.values())
    new['form_decoder_splice'] = {
        'removed_rows': cut, 'removed_digest': digest(cut),
        'new_decoder_rows': decode, 'new_form_rows': forms,
        'literal_retained_row_names': [row[0] for row in outside],
        'old_source_digest': digest(old['source']), 'new_source_digest': digest(new['source']),
        'unchanged_form_exit_names': sorted(exits), 'external_form_consumers': external,
        'retired_fixed_roles': sorted(retired), 'introduced_fixed_roles': sorted(introduced),
        'canonical_recipe_required': True,
        'finalizer_literal_equal': True, 'comparisons_literal_equal': new['comparisons'] == old['comparisons'],
        'positive_auxiliaries_literal_equal': new['positive_auxiliaries'] == old['positive_auxiliaries'],
        'lanes_literal_equal': new['lanes_in_order'] == old['lanes_in_order'],
    }
    examples.append(new)

assert [g['r'] for g in examples] == [1, 2, 4]
assert sum(len(g['source']) for g in examples) == 2716
recipe = [
    'For each fixed noncentral relator P=[p,q;s,t], normalize (2q,p-t,-2s) to primitive w. Choose k as the first nonzero ORIGINAL coordinate; permute by transposition(1,k) only.',
    'In that order put g=gcd(w1,w2)>0, choose integers a,b with a*w1+b*w2=g, u=(w2/g,-w1/g,0), v=(-w3*a,-w3*b,g); undo the same transposition. Then original-order u3=0.',
    'Central P=+/-I uses original-order u=e1,v=e2, Eplus=0, w=e3,c=e3^T,J0=first2 identity columns,T=I2; never normalize the zero invariant.',
    'Use exactly this SAME V=[u;v] to prepare old ell=V*C, Eplus and quotient_T. C=[1,0,0,-1;1,1,0,-2;2,0,1,-4]. A=S(P) obeys A-I=Eplus*V.',
    'Choose fixed integer row c with c*w=1 for the ORIGINAL-order primitive w after undoing the preparatory transposition; set U=[u;v;c] and J0=first2 columns of U inverse. Then V*J0=I2, quotient_T=V*S(P inverse)*J0, and Eminus=-Eplus*quotient_T.',
    'Keep lambda=1+max(0,negative ell entries), Cg=2lambda+1, and dyadic K>max(Cmass,m,Cg,lambda+pplus), with pplus=max(0,ell entries). These are prepared from actual ell even though ell no longer appears as runtime multiplication roles.',
    'Runtime roles use original-order u1,u2,v1,v2,v3 as form_basis_u/v, plus the SAME6 positive-sign relator_E and4 quotient_T entries per relator and6 unchanged global roles. All zero/unit coefficient products remain paid.',
    'Parent/child polynomial equality holds for matching fixed recipes using this canonical V throughout; it does not identify independent old/new coefficients or reinterpret a differently prepared parent V. Ordinary input, positive witnesses, guard and all consumers remain unchanged.',
]
result = {
    'status': 'FROZEN first original metadata-only shared-decoder composition; never replay',
    'emitter_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    'inputs': [{'path': str(PARENT), 'sha256': sha256(raw).hexdigest(), 'bytes': len(raw)}],
    'generic_ledger': {
        'domain': 'r>=1; same canonical actual-relator recipe throughout',
        'certificate': '(201+30r+gM(8+2r))M+(464+41r+gA(8+2r))A',
        'polynomial': '(224+30r+gM(8+2r))M+(509+41r+gA(8+2r))A',
        'operations': '733+71r+gM(8+2r)+gA(8+2r)',
        'native_scale_products': 4, 'witnesses': '96+6r', 'equations': 23, 'fixed_roles': '6+15r',
        'geometric_cost': parent['generic_ledger']['geometric_cost'],
    },
    'fixed_data_recipe': recipe, 'r0_fallback': parent['r0_fallback'], 'examples': examples,
    'execution_scope': 'Only inert-record construction, label counts, byte equality and dependencies/liveness. No saved arithmetic or coefficient evaluation, degree propagation, scientific sampling, imported predecessor, frozen replay or build.',
}
OUT.write_text(json.dumps(result, indent=2) + '\n')
print('PASS first-only metadata emission: 2716 rows; 812/878/1026 operations; now frozen')
