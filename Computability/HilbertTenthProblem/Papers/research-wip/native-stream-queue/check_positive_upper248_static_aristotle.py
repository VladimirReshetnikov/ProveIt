"""Independent pre-freeze static248 audit; no program/array evaluation.

Read only frozen parent data and author's new data. No predecessor import,
numeric source interpreter, polynomial interpreter, or degree propagation.
Do not replay after this review is frozen.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
BASE = Path('/tmp/neary_woods_positive_upper248_tesla')
PARENT_SHA = 'e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c'
CORRECTION_SHA = '573effd459ea14b1ca82b98cc3a61a5ba37e41ada68965200cf382f35ebe1366'


def ensure(ok, why):
    if not ok:
        raise ValueError(why)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def atom_names(row):
    return [x for x in row[2:] if type(x) is str]


def source_map(rows):
    result = {r[0]: r for r in rows}
    ensure(len(result) == len(rows), 'distinct identifiers')
    return result


def graph_audit(rows, ports, roles, output):
    available = set(ports)
    ensure(len(available) == len(ports), 'distinct supplied ports')
    defs = source_map(rows)
    uses = {}
    seen_roles = set()
    for row in rows:
        ensure(len(row) == 4, 'producer arity')
        name, op, left, right = row
        ensure(name not in available and op in ('+', '-', '*'), 'producer format')
        for a in (left, right):
            if type(a) is str:
                ensure(a in available, 'unpaid or late dependency: ' + name)
                uses.setdefault(a, set()).add(name)
            elif type(a) is int:
                pass
            else:
                ensure(type(a) is dict and set(a) == {'fixed_numeral'}, 'fixed numeral format')
                ensure(a['fixed_numeral'] in roles, 'unknown fixed role')
                seen_roles.add(a['fixed_numeral'])
        available.add(name)
    closure = set()
    pending = [output]
    while pending:
        x = pending.pop()
        if x in closure:
            continue
        closure.add(x)
        if x in defs:
            pending.extend(atom_names(defs[x]))
    ensure(set(defs) | set(ports) == closure, 'complete output liveness')
    ensure(seen_roles == set(roles), 'complete numeral liveness')
    operations = Counter(r[1] for r in rows)
    return {
        'M': operations['*'], 'A': operations['+'] + operations['-'],
        'rows': len(rows), 'live_supplied_ports': len(ports),
        'live_fixed_roles': len(seen_roles), 'all_live': True,
        'row_digest': sha(json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()),
    }, {k: sorted(v) for k, v in uses.items()}


def inspect(parent, child):
    old = source_map(parent['source'])
    actual = source_map(child['source'])
    edits = {
        'hist__global_sum__12': ['hist__global_sum__12', '+', 'hist__ZU0', 'hist__global_sum__11'],
        'hist__linear0_coefficient__17': ['hist__linear0_coefficient__17', '*', 'hist__ZU0', {'fixed_numeral': 'upper_difference'}],
        'hist__pack_sum__63': ['hist__pack_sum__63', '+', 'tree_group12', 'hist__pack_product__62'],
        'hist__repunit_tail__64': ['hist__repunit_tail__64', '+', 'hist__P2__51', 'hist__P__10'],
        'hist__pack_sum__73': ['hist__pack_sum__73', '+', 'hist__ZU0', 'hist__pack_product__72'],
    }
    old_edits = {
        'hist__global_sum__12': ['hist__global_sum__12', '+', 'hist__ZUhat0', 'hist__global_sum__11'],
        'hist__linear0_coefficient__17': ['hist__linear0_coefficient__17', '*', 'hist__ZUhat0', {'fixed_numeral': 'upper_difference'}],
        'hist__pack_sum__63': ['hist__pack_sum__63', '+', 'hist__group_hat__59', 'hist__pack_product__62'],
        'hist__repunit_tail__64': ['hist__repunit_tail__64', '+', 'hist__P2__51', 'hist__repunit_factor__50'],
        'hist__pack_sum__73': ['hist__pack_sum__73', '+', 'hist__ZUhat0', 'hist__pack_product__72'],
    }
    for n, r in old_edits.items():
        ensure(old[n] == r, 'old changed-cut binding')
    deleted = ['hist__group_hat__59', '-', 'hist__group_sum__58', 1]
    ensure(old[deleted[0]] == deleted, 'deleted paid subtraction')
    expected = dict(old)
    del expected[deleted[0]]
    expected.update(edits)
    ensure(actual == expected, 'all248 expected producer definitions')
    ensure(sum(old.get(n) == r for n, r in actual.items()) == 243, 'literal retention')
    recipes = dict(parent['fixed_numeral_recipes'])
    ensure(recipes['upper_constant'] == '2^(beta+3)+2', 'old upper constant')
    ensure(recipes['upper_difference'] == '2^(beta+2)-2', 'old upper difference')
    recipes['upper_constant'] = '2^(beta+2)+4'
    ensure(child['fixed_numeral_recipes'] == recipes, 'exact fixed recipe change')
    for key in ('parameters', 'domains', 'fixed_u9_recipe', 'merged', 'output', 'comparisons'):
        ensure(child[key] == parent[key], 'inherited interface ' + key)
    expected_aux = ['hist__ZU0' if x == 'hist__ZUhat0' else x for x in parent['auxiliaries']]
    ensure(child['auxiliaries'] == expected_aux and len(expected_aux) == 43, 'all43 witness roles')
    ensure(child['domains'] == {'auxiliaries': 'positive integers', 'parameters': 'positive integers; program parameters fixed on valid shifted program slices'}, 'no stale named domain')
    expected_params = ['x', 'program_A', 'program_B', 'program_T', 'program_E']
    if not child['merged']:
        expected_params.append('program_bound')
    ensure(child['parameters'] == expected_params, 'ordinary input and fixed program interface')
    prior, prior_uses = graph_audit(parent['source'], parent['parameters'] + parent['auxiliaries'], recipes, parent['output'])
    ledger, uses = graph_audit(child['source'], child['parameters'] + child['auxiliaries'], recipes, child['output'])
    ensure((prior['rows'], prior['M'], prior['A']) == (249, 129, 120), 'parent ledger')
    ensure((ledger['rows'], ledger['M'], ledger['A']) == (248, 129, 119), 'child ledger')
    ensure(ledger['live_fixed_roles'] == 11, 'fixed recipe arity')
    ensure(child['ledger']['canonical_source_sha256'] == ledger['row_digest'], 'author source digest')
    ensure(child['parent_source_sha256'] == prior['row_digest'], 'parent row digest')
    private = {
        'hist__ZUhat0': ['hist__global_sum__12', 'hist__linear0_coefficient__17', 'hist__pack_sum__73'],
        'hist__global_bound': ['hist__P__10'],
        'hist__global_sum__12': ['hist__global_sum__13'],
        'hist__global_sum__13': ['hist__global_sum__14'],
        'hist__global_sum__14': ['hist__P__10'],
        'hist__linear0_coefficient__17': ['hist__linear0_sum__20'],
        'hist__linear0_sum__20': ['hist__linear_sum__166'],
        'hist__linear_sum__166': ['hist__linear_sum__167'],
        'hist__linear_sum__167': ['hist__linear_constant__168'],
        'hist__group_hat__59': ['hist__pack_sum__63'],
        'hist__pack_sum__63': ['hist__unhat_pack__65'],
        'hist__repunit_tail__64': ['hist__unhat_pack__65', 'hist__unhat_pack__74'],
        'hist__pack_sum__73': ['hist__unhat_pack__74'],
    }
    for n, wanted in private.items():
        ensure(prior_uses[n] == wanted, 'all affected old consumers ' + n)
        if n not in ('hist__ZUhat0', 'hist__group_hat__59'):
            ensure(uses[n] == wanted, 'all affected new consumers ' + n)
    ensure(uses['hist__ZU0'] == private['hist__ZUhat0'], 'new selected-word consumers')
    for data in [old, actual]:
        constant_uses = [n for n, r in data.items() if {'fixed_numeral': 'upper_constant'} in r[2:]]
        ensure(constant_uses == ['hist__linear_constant__168'], 'changed coefficient consumer')
    exit_names = ['hist__P__10', 'hist__unhat_pack__65', 'hist__unhat_pack__74', 'hist__linear_constant__168']
    for n in exit_names + ['hist__repunit_factor__50', 'hist__P2__51', 'tree_group12']:
        ensure(actual[n] == old[n], 'unchanged cut-exit row')
    factors = [prefix + tail for prefix in ['geo__', 'and__']
               for tail in ['R15', 'P17', 'first_unit', 'f_square_minus_one', 'index_unit', 'linear_unit']]
    factors += ['mask_repunit_unit', 'history_upper_unit', 'history_global_unit', 'lower_history_unit']
    spine = []
    leaves = []
    stack = ['lower_history_product']
    while stack:
        n = stack.pop()
        if n in factors:
            leaves.append(n)
        else:
            r = actual[n]
            ensure(r[1] == '*' and all(type(a) is str for a in r[2:]), 'literal final product spine')
            ensure(r == old[n], 'retained final product row')
            spine.append(n)
            stack.extend(r[2:])
    ensure(Counter(leaves) == Counter(factors) and len(spine) == 15, 'all16 factors once')
    ensure(actual['lower_unit_output'] == ['lower_unit_output', '-', 'lower_history_product', 'geo__A'], 'complete final subtraction')
    ensure(child['certificate'] == {'total':247,'M':129,'A':118,'comparisons':1,'positive_witnesses':43}, 'certificate accounting')
    ensure(child['manual_degree_upper_bound'] == 936 and child['exact_degree_claimed'] is False, 'corrected degree scope')
    ensure(not any('hist__ZUhat0' in r for r in child['source']), 'no old hat source operand')
    return {'merged':child['merged'], 'ledger':ledger, 'parameters':expected_params,
            'auxiliaries':expected_aux, 'fixed_numeral_recipes':recipes,
            'deleted_row':deleted, 'edited_rows':list(edits.values()),
            'literal_retained_row_records':243, 'numerically_changed_literal_record':'hist__linear_constant__168',
            'full_old_changed_cone_consumers':private, 'manual_identity_cut_exits':exit_names,
            'complete_finalizer':{'product_rows':len(spine),'factors':sorted(leaves),'subtracted':'geo__A'},
            'degree_scope':'936 inherited from corrected geometry-only249 through affine substitution; no propagation'}


def main():
    parent_path = WIP / 'neary_woods_scaled_strong249_tesla.json'
    correction_path = WIP / 'neary_woods_scaled_strong249_degree_correction_tesla.json'
    parent_raw = parent_path.read_bytes()
    ensure(sha(parent_raw) == PARENT_SHA, 'actual parent JSON')
    ensure(sha(correction_path.read_bytes()) == CORRECTION_SHA, 'required parent correction')
    parent = json.loads(parent_raw)
    child = json.loads(BASE.with_suffix('.json').read_bytes())
    deps = []
    for rec in child['dependencies']:
        raw = (ROOT / rec['path']).read_bytes()
        ensure(sha(raw) == rec['sha256'] and len(raw) == rec['bytes'], 'author dependency binding')
        deps.append(rec)
    ensure(child['helper_sha256'] == sha(BASE.with_suffix('.py').read_bytes()), 'author helper byte binding')
    parents = {f['merged']:f for f in parent['forms'] if f['cores_scaled'] == ['geo__']}
    children = {f['merged']:f for f in child['forms']}
    ensure(set(parents) == set(children) == {False, True}, 'both interfaces')
    results = [inspect(parents[m], children[m]) for m in [False, True]]
    a = source_map(children[False]['source'])
    b = source_map(children[True]['source'])
    ensure([n for n in a if a[n] != b[n]] == ['program_duration_bound'], 'only inter-interface source difference')
    ensure(sha(parent_path.read_bytes()) == PARENT_SHA, 'parent immutable after audit')
    output = {
        'status':'PASS: independent source-only/static audit',
        'checker_sha256':sha(Path(__file__).read_bytes()),
        'author_artifacts':[{'path':str(BASE.with_suffix(ext)), 'sha256':sha(BASE.with_suffix(ext).read_bytes())}
                            for ext in ['.md','.py','.json']],
        'dependencies':deps, 'forms':results, 'checked_child_rows':496,
        'operation_saving':'one subtraction per source; 249=129M120A ->248=129M119A',
        'execution_limits':'Fresh static metadata only; no saved source-array execution, numeric or symbolic interpretation, degree propagation, or predecessor import/execution. No replay after freeze.',
        'proof_scope':'Four cut identities verified manually in reviewer note; positive-zero extension belongs to separate root semantic review.'}
    dest = Path('/tmp/positive_upper248_static_read_aristotle.json')
    dest.write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    print('PASS: two full248 arrays, 496 rows,43 witnesses,11 numeral roles,15 products and16 factor leaves per interface.')


if __name__ == '__main__':
    main()
