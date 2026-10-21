"""Owned composition and independent integrity checks; input JSON is inert."""
from pathlib import Path
import hashlib, json

D = Path(__file__).resolve().parent
ROOT = D.parent
P = ROOT / 'research217_review/contextual/selected/machine'
H = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())
B = read(D / 'BOOT_RESULT.json')
R = read(D / 'RUNTIME_RESULT.json')
C = read(D / 'CASES.json')
S = read(ROOT / 'research217_encoding/CONTEXTUAL_ALTERNATE_COMPARISON.json')
A = read(ROOT / 'research218_published_encoding/CONSTRUCTION_AUDIT.json')
sites = read(P / 'sites218.json')

assert B['status'] == 'INDEPENDENT_SPARSE_NATIVE_AND_DENSE_CANONICAL_BOOT_PASS'
assert R['status'] == 'FRESH_OWNED_KERNEL_FULL_CONTEXTUAL_K218_RUNTIME_PASS'
assert A['status'] == 'PASS'
for rel, digest in A['input_pins'].items():
    assert H(ROOT / rel) == digest, rel
for rel, digest in R['input_pins'].items():
    assert H(ROOT / rel) == digest, rel
assert R['table_sha256'] == B['native_sha256'] == S['alternate_table_sha256'] == H(P / 'k218.native.tm')
assert R['source_sha256'] == B['source_sha256'] == S['alternate_source_sha256'] == H(P / 'sites218.json')
assert S['primary_source_sha256'] == A['input_pins']['latest218_baseline/candidate-k218/sites218.json']
assert S['primary_table_sha256'] == A['input_pins']['latest218_baseline/candidate-k218/k218.native.tm']
assert S['ordered_primitive_operations_and_arguments_equal'] and S['same_ordinal_cfg']
assert S['two_independent_cfg_resolvers_agree'] and S['both_prefix_bindings_complete']
assert S['primitive_occurrences'] == 4744 and S['guarded_successor_edges'] == 6166

expected = [(i, positive) for i, (pc, op, arg) in enumerate(sites)
            for positive in ((False, True) if op == 'CD' else (False,))]
assert [(c['index'], c['positive']) for c in C] == expected
assert len(C) == R['cases'] == 6167
assert sum(c['symbolic_steps'] for c in C) == R['rules'] == 1514325
assert min(c['duration'][0] for c in C) == R['minimum_duration'] == 13
assert R['row_coverage'] == 436
assert all(len(c['duration']) == 13 and c['duration'][0] > 0
           and all(type(x) is int and x >= 0 for x in c['duration'])
           and sum(c['kinds'].values()) == c['symbolic_steps'] for c in C)
assert R['cases_sha256'] == H(D / 'CASES.json')
claimed = read(P.parent / 'certificates/runtime/integrity.json')
assert H(D / 'CASES.json') == claimed['hashes']['cases.json']

# Check the fresh native-to-kernel map against all inert normalized-table
# runtime-map entries, after the independently verified native relabeling.
runtime_map = {int(k): v for k, v in read(D / 'NATIVE_TO_RUNTIME.json').items()}
claimed_map = {int(k): v for k, v in read(P.parent / 'certificates/runtime/runtime.json')['mapping'].items()}
normal = lambda q: {301: 102, 302: 120}.get(q, q)
assert {normal(q): z for q, z in runtime_map.items()} == claimed_map
assert len(runtime_map) == len(set(runtime_map.values())) == 219
assert B['logical'] == [3,0,0,0,3,0,0,0,0] and B['steps'] == 312701
assert B['all_other_cells_zero'] and B['no_earlier_halt']
assert B['all_transition_counts_sparse_dense_equal'] and B['normalized_isomorphism']
assert B['bfs_isomorphism'] and B['all_graph_reachable']

pins = [D / 'BOOT_RESULT.json', D / 'RUNTIME_RESULT.json', D / 'CASES.json',
        D / 'NATIVE_TO_RUNTIME.json', D / 'CANONICAL_MAP.json',
        ROOT / 'research217_encoding/CONTEXTUAL_ALTERNATE_COMPARISON.json',
        ROOT / 'research217_encoding/compare_contextual.py',
        ROOT / 'research218_published_encoding/CONSTRUCTION_AUDIT.json',
        ROOT / 'research218_baseline_audit/REPORT.md',
        ROOT / 'research218_baseline_audit/PEDIGREE_AUDIT.json']
result = dict(
    status='CONTEXTUAL_218_BLANK_SUBSTRATE_INDEPENDENT_AUDIT_PASS',
    native_sha256=R['table_sha256'], canonical_sha256=B['canonical_sha256'],
    normalized_sha256=B['normalized_sha256'], source_sha256=R['source_sha256'],
    cases_sha256=H(D / 'CASES.json'), matches_received_case_hash=True,
    working_states=218, transition_rows=436, blank_steps=312701,
    guarded_cases=6167, symbolic_rules=1514325, minimum_duration=13,
    source_leaves=4744, source_dag_nodes=205,
    ordinary_theorem='ZFC proves: Halt(exact contextual K218, blank) iff ZFC has a finite refutation; equivalently, not Halt(exact contextual K218, blank) iff Con(ZFC).',
    calibration_dependency='Accepted K219 finite-refutation calibration and ancestor pedigree, transported through the independently audited published K218 source and the exact contextual source CFG identity; fresh contextual runtime and blank initialization.',
    current_target_states=217, current_target_met=False,
    scope_limits=['No unconditional nonhalting or proof of Con(ZFC).',
                  'No new Lean/Rocq/internal-PA endpoint for these exact bytes.',
                  'No minimality claim; this is not a 217-state candidate.',
                  'Runtime quantification over arbitrary registers does not license unsound dirty formula/cache seeds.'],
    no_received_code_execution=True, no_ancestor_build=True,
    dependencies={str(p.relative_to(ROOT)): H(p) for p in pins},
    driver_sha256=H(Path(__file__)))
(D / 'COMPOSED_RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
