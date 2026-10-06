"""Original metadata-only alias composer, for one run and permanent freeze.

Records are copied/rebound/count-labelled; no instruction is evaluated.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
INPUT = ROOT / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/positive7_shared_decoder_compiler_root.json'
OUTPUT = Path('/tmp/positive7_power_alias_compiler_root.json')
assert not OUTPUT.exists(), 'Never replay a frozen composer'
raw = INPUT.read_bytes()
assert sha256(raw).hexdigest() == 'e6539f0c8b8d66b53537d228425932a0a3d030e78d5f96be0d68d513ebe20b95'
parent = json.loads(raw)


def fingerprint(value):
    return sha256(json.dumps(value, separators=(',', ':')).encode()).hexdigest()


def label_count(rows):
    labels = Counter(row[1] for row in rows)
    assert set(labels) <= {'*', '+', '-'}
    return dict(M=labels['*'], A=labels['+']+labels['-'], operations=len(rows))


def aliases_for(m):
    bits = bin(m)[2:]
    assert m >= 10 and m % 2 == 0
    A = int(bits.startswith('101'))
    B = int(bits.startswith('1110') and len(bits) >= 5)
    C = int(bits.startswith('10011'))
    assert A+B+C <= 1
    if bits.startswith('110'):
        links = {'left_support_P12': 'geom_P12', 'left_pair_factor_6': 'geom_factor_12'}
    elif bits.startswith('111'):
        links = {'left_support_P14': 'geom_P14', 'left_pair_factor_7': 'geom_factor_14'}
    else:
        assert bits.startswith('10')
        links = {'left_support_P4': 'geom_P4', 'left_pair_factor_2': 'geom_factor_4'}
    if A:
        links['left_support_P5'] = 'geom_P5'
    if B:
        links.update(left_support_P28='geom_P28', left_pair_factor_14='geom_factor_28')
    if C:
        links['native_shared_P19'] = 'geom_P19'
    return links, dict(A=A, B=B, C=C)


graphs = []
expected = {1: (257, 552), 2: (285, 591), 4: (349, 675)}
for old in parent['examples']:
    r = old['r']; links, flags = aliases_for(old['m'])
    positions = {row[0]: i for i, row in enumerate(old['source'])}
    by_name = {row[0]: row for row in old['source']}
    for removed, target in links.items():
        assert positions[target] < positions[removed]
    removed_rows = []; rebound = []; literal = []; stages = {}; output_rows = []
    offset = 0
    for stage, declared in old['stages'].items():
        block = old['source'][offset:offset+declared['operations']]
        offset += len(block)
        assert label_count(block) == declared
        retained = []
        for row in block:
            if row[0] in links:
                removed_rows.append(row)
                continue
            updated = row[:2] + [links.get(x, x) if isinstance(x, str) else x for x in row[2:]]
            if updated == row:
                literal.append(row[0])
            else:
                rebound.append(dict(before=row, after=updated))
            retained.append(updated)
        stages[stage] = label_count(retained)
        output_rows.extend(retained)
    assert offset == len(old['source'])
    A, B, C = (flags[x] for x in ('A', 'B', 'C'))
    assert label_count(removed_rows) == dict(M=1+A+B+C, A=1+B, operations=2+A+2*B+C)
    assert output_rows[-68:] == old['source'][-68:]
    new = deepcopy(old)
    del new['form_decoder_splice']
    new['source'] = output_rows
    new['stages'] = stages
    new['polynomial_ledger'] = label_count(output_rows)
    new['certificate_ledger'] = label_count(output_rows[:-68])
    new['certificate_prefix_rows'] = len(output_rows)-68
    assert (new['polynomial_ledger']['M'], new['polynomial_ledger']['A']) == expected[r]
    new['native_scale_products'] = 4-C

    def replace_values(obj):
        if isinstance(obj, str):
            return links.get(obj, obj)
        if isinstance(obj, list):
            return [replace_values(x) for x in obj]
        if isinstance(obj, dict):
            return {k: replace_values(v) for k, v in obj.items()}
        return obj

    new['ports'] = replace_values(old['ports'])
    supplied = set(new['ordinary_parameters'] + new['positive_auxiliaries'])
    known = set(supplied); fixed = Counter(); uses = {}; definitions = {}
    for name, op, left, right in output_rows:
        assert name not in known and op in ('*', '+', '-')
        for operand in (left, right):
            if isinstance(operand, str):
                assert operand in known
            elif isinstance(operand, dict):
                assert set(operand) == {'fixed'}
                role = operand['fixed']; fixed[role] += 1; uses[role] = op
            else:
                assert type(operand) is int
        definitions[name] = (left, right); known.add(name)
    live = {new['output']}
    for name, _, left, right in reversed(output_rows):
        if name in live:
            live.update(x for x in (left, right) if isinstance(x, str))
    assert set(definitions) <= live and supplied <= live
    assert set(fixed.values()) == {1} and sorted(fixed) == old['static_checks']['named_fixed_roles']
    assert len(fixed) == 6+15*r and {k: v for k, v in uses.items() if v != '*'} == {'gamma': '+'}
    assert not (set(links) & known)
    new['static_checks'] = dict(topology=True, all_computed_live=True, all_supplied_live=True, named_fixed_roles=sorted(fixed))
    changes = {k: dict(before=old['ports'][k], after=v) for k, v in new['ports'].items() if old['ports'][k] != v}
    new['pack_power_alias_splice'] = dict(
        aliases=links, indicators=flags, removed_rows=removed_rows,
        existing_target_records=[by_name[t] for t in links.values()],
        literal_retained_row_names=literal, rebound_rows=rebound,
        old_source_digest=fingerprint(old['source']), new_source_digest=fingerprint(output_rows),
        removed_digest=fingerprint(removed_rows), changed_ports=changes,
        added_arithmetic_rows=0, removed_ledger=label_count(removed_rows),
        fixed_roles_literal_equal=True, positive_auxiliaries_literal_equal=True,
        comparisons_literal_equal=True, finalizer_literal_equal=True,
        general_unemitted_cases='No complete seed7/B/C parent examples exist in this input; their all-r grammar is proved separately, not claimed as saved-row coverage.')
    graphs.append(new)

assert [g['r'] for g in graphs] == [1, 2, 4]
assert sum(len(g['source']) for g in graphs) == 2709
result = dict(
    status='FROZEN first original metadata-only alias composition; never replay',
    emitter_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    inputs=[dict(path=str(INPUT), sha256=sha256(raw).hexdigest(), bytes=len(raw))],
    generic_ledger=dict(
        domain='r>=1 with inherited canonical fixed recipe; A=prefix101, B=prefix1110 with at least5 bits, C=prefix10011 of m=8+2r',
        certificate='(200+30r+gM-A-B-C)M+(463+41r+gA-B)A',
        polynomial='(223+30r+gM-A-B-C)M+(508+41r+gA-B)A',
        operations='731+71r+gM+gA-A-2B-C', native_scale_products='4-C',
        witnesses='96+6r', equations=23, fixed_roles='6+15r',
        geometric_cost=parent['generic_ledger']['geometric_cost']),
    fixed_data_recipe=parent['fixed_data_recipe'], r0_fallback=parent['r0_fallback'], examples=graphs,
    execution_scope='Only record construction, alias substitution, literal/label counts, source hashes, topology and liveness. No instruction/coefficient evaluation, symbolic propagation, degree calculation, scientific sampling, imported/replayed helper or build.')
OUTPUT.write_text(json.dumps(result, indent=2)+'\n')
print('PASS first-only metadata alias composition: 2709 rows, 809/876/1024; freeze source and receipt')
