#!/usr/bin/env python3
"""Offline reproduction of the fixed-point engineering supplement.

--quick regenerates both selected controls, independently verifies their finite
operation certificates, checks every supplied pinned input, and reproduces the
253-state literal table correspondence and finite blank bootstrap.
--full-search additionally recompiles all 20,480 selected grammar candidates.
--fusion additionally repeats the bounded 148,368-candidate fusion experiment.
Only Python's standard library is required. No network or Git command is used.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
import csv
import gzip
import hashlib
import importlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE / 'vendor/ProveIt'
RESEARCH = REPO / 'Computability/BusyBeaver/Research/ZFC'
CODE = REPO / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code'
SNAPSHOT = REPO / 'lib/jeff-busy-beaver-zfc254'
SELECTED = ('EPSC_s', 'EFPC_010')


def read_json(path):
    return json.loads(path.read_text())


def write_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run_python(script, arguments, cwd=None):
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                            cwd=cwd or HERE, env=environment, text=True,
                            capture_output=True)
    if result.returncode:
        raise RuntimeError(f'{script.name} failed:\n{result.stdout}\n{result.stderr}')
    return result.stdout


def check_sources():
    entries = read_json(HERE / 'SOURCE_MANIFEST.json')['files']
    for record in entries:
        path = HERE / record['path']
        require(path.is_file(), f'Missing pinned source: {record["path"]}')
        require(path.stat().st_size == record['bytes'], f'Size mismatch: {record["path"]}')
        require(sha(path) == record['sha256'], f'SHA-256 mismatch: {record["path"]}')
    return {'pinned_files_verified': len(entries)}


def baseline_check(audit):
    old = audit.parse_table((SNAPSHOT / 'ZF/m254/machine/zfc_254.tm').read_text())
    compact_path = HERE / 'baseline/zfc_253.tm'
    compact = audit.parse_table(compact_path.read_text())
    rows = {(q, b): (e.write, e.move, e.target) for (q, b), e in old.rows.items() if q != 8}
    rows.update({(3, 0): (0, -1, 48), (5, 0): (1, 1, 97),
                 (5, 1): (1, 1, 64), (49, 1): (0, 1, 5)})
    mapping = {5: compact.start}
    pending = deque([5])
    while pending:
        q = pending.popleft()
        if q == 254:
            require(mapping[q] == compact.halt, 'Terminal correspondence differs')
            continue
        for bit in (0, 1):
            write, move, target = rows[q, bit]
            actual = compact.rows[mapping[q], bit]
            require((write, move) == (actual.write, actual.move), 'Row action differs from old-label delta')
            if target in mapping:
                require(mapping[target] == actual.target, 'Inconsistent old/compact correspondence')
            else:
                mapping[target] = actual.target
                pending.append(target)
    require(set(mapping) == set(range(255)) - {8}, 'Old-label coverage incomplete')
    require(set(mapping.values()) == set(range(254)), 'Compact correspondence is not bijective')
    require(mapping[96] == 33, 'Dispatcher label differs')
    target = read_json(HERE / 'baseline/bootstrap_253.json')
    q, head, ones = compact.start, 0, set()
    for _ in range(target['steps']):
        edge = compact.rows[q, int(head in ones)]
        if edge.write:
            ones.add(head)
        else:
            ones.discard(head)
        head += edge.move
        q = edge.target
    require((q, head, sorted(ones)) == (target['state'], target['head'], target['ones']),
            'Whole finite bootstrap endpoint differs')
    require(target['ones_relative_to_head'] == sorted(x - head for x in ones), 'Relative bootstrap coordinates differ')
    return {'working_states': len(compact.states), 'transition_rows': len(compact.rows),
            'literal_sha256': sha(compact_path), 'complete_old_compact_bijection': True,
            'old_labels_changed_rows': 4, 'old_labels_deleted_state': 8,
            'bootstrap_steps': target['steps'], 'bootstrap_state': q,
            'bootstrap_head': head, 'bootstrap_one_cells': len(ones),
            'complete_finite_tape_match': True,
            'kernel_proof_or_internalization_rebuilt': False}


def total_bytes(machine):
    states = {q for q, _ in machine.states}
    ordered = [machine.start] + sorted(states - {machine.start})
    missing = [(q, b) for q in states for b in ('0', '1') if (q, b) not in machine.states]
    require(missing == [('1.inc', '1')], 'Unexpected partial source transition')
    labels = {q: i for i, q in enumerate(ordered)}
    labels['halt'] = len(ordered)
    lines = ['#! start 0']
    for q in ordered:
        for bit in ('0', '1'):
            edge = machine.states.get((q, bit))
            write, direction, dest = ((bit, 'R', labels['halt']) if edge is None else
                                      (edge.write, edge.direction, labels[edge.nextstate]))
            lines.append(f'{labels[q]} {bit} {write} {direction} {dest}')
    return ('\n'.join(lines) + '\n').encode(), ordered


def check_controls(scratch, audit):
    sys.path.insert(0, str(RESEARCH))
    import theory_backend_experiment as theory
    import recover_wade_dag as recover
    schema = load('engineering_measure', HERE / 'measure_fixedpoint.py')
    grammar = load('engineering_grammar', CODE / '14-empty-third_party-one_schema-machine-rebracket_axioms.py')
    macros = load('engineering_macros', CODE / '14-empty-code-macro_contract.py')
    sys.path.insert(0, str(SNAPSHOT / 'ZF/generator'))
    backend = importlib.import_module('TMBuilder')
    nodes, names = recover.parse_dag(recover.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    effects = macros.possible_returns(nodes)
    require(all(effects[q] == {macros.NORMAL} for q in macros.MACROS), 'An emission macro is not closed')
    spec, _ = theory.published_spec()
    original = spec['ax_rows']('a', 'h', 'b', 'c', 'u')
    membership_vacuity = theory.Imp(theory.Rel('a', 'b'), theory.All('c', theory.Rel('a', 'b')))
    equality_vacuity = theory.Imp(theory.Eq('a', 'b'), theory.All('c', theory.Eq('a', 'b')))
    results = []
    checker = CODE / '14-empty-code-verify_operation_certificate.py'
    for mode in SELECTED:
        stored = HERE / 'fixedpoint' / mode
        generated = scratch / mode
        generated.mkdir()
        expected = read_json(stored / 'results.json')
        recipe = expected['recipe']
        formula = schema.formula(theory, mode)
        bundle = (theory.And(theory.And(formula, equality_vacuity), membership_vacuity)
                  if recipe['association'] == 0 else
                  theory.And(formula, theory.And(equality_vacuity, membership_vacuity)))
        word = [166, 121, 180, 176]
        for i in recipe['logical_order']:
            word += theory.emit(original[i])
        word += theory.emit(bundle) + theory.TAIL
        wanted = ['old_top', original[0]] + [original[i] for i in recipe['logical_order']] + [bundle]
        require(theory.symbolic(word)[0] == wanted, 'Constructed logical/theory rows differ')
        sequence, productions = grammar.repair(word, recipe['seed'], recipe['alpha'])
        new_nodes, new_names, new_root = grammar.transform(nodes, names, sequence, productions)
        machine = grammar.compile_dag(backend, new_nodes, new_names)
        grammar.reextract(machine, new_nodes, new_names)
        machine.save(str(generated / 'winner_named.tm'))
        data, ordered = total_bytes(machine)
        (generated / 'winner_total.tm').write_bytes(data)
        naive, naive_names, naive_root = grammar.transform(nodes, names, word, [])
        certificate, _ = grammar.bisimulation(naive, new_nodes)
        regenerated = {
            'source_dag.json': {'root': 0, 'axioms_root': naive_root, 'nodes': naive, 'names': naive_names},
            'candidate_dag.json': {'root': 0, 'axioms_root': new_root, 'nodes': new_nodes, 'names': new_names},
            'rm_bisimulation.json': certificate,
            'grammar.json': {'word': word, 'seq': sequence, 'grammar': productions},
            'state_names.json': {'states': ordered, 'halt': len(ordered)},
        }
        for filename, value in regenerated.items():
            write_json(generated / filename, value)
        for filename in ('winner_named.tm', 'winner_total.tm', *regenerated):
            require((generated / filename).read_bytes() == (stored / filename).read_bytes(),
                    f'{mode}/{filename} did not regenerate byte for byte')
        check_output = generated / 'independent_rm_check.json'
        run_python(checker, ['--source', generated / 'source_dag.json',
                            '--candidate', generated / 'candidate_dag.json',
                            '--certificate', generated / 'rm_bisimulation.json',
                            '--output', check_output])
        independent = read_json(check_output)
        require(independent['verified'], 'Independent operation verification failed')
        if (stored / 'independent_rm_check.json').exists():
            require(independent == read_json(stored / 'independent_rm_check.json'), 'Independent certificate report differs')
        parsed = audit.parse_table(data.decode())
        reachable = audit.graph_reachable(parsed)
        require(len(parsed.states) == expected['working_states'], 'Literal state count differs')
        require(len(parsed.rows) == expected['total_rows'], 'Literal row count differs')
        require(len(reachable - {parsed.halt}) == len(parsed.states), 'Unreachable counted state')
        require(sha(generated / 'winner_total.tm') == expected['literal_sha256'], 'Literal table hash differs')
        results.append({'mode': mode, 'working_states': len(parsed.states), 'transition_rows': len(parsed.rows),
                        'source_decision_nodes': len(naive), 'decision_states': len(new_nodes),
                        'literal_sha256': expected['literal_sha256'], 'all_generated_files_byte_identical': True,
                        'independent_operation_check': independent,
                        'all_counted_states_graph_reachable': True})
    return results


def check_recorded_fusion():
    recorded = read_json(HERE / 'fusion/fusion_results.json')
    data = gzip.decompress((HERE / 'fusion/rejection_ledger.csv.gz').read_bytes())
    rows = list(csv.DictReader(io.StringIO(data.decode())))
    census = Counter(row['reason'] for row in rows)
    require(len(rows) == recorded['tested'] == 148368, 'Fusion ledger count differs')
    require(dict(census) == recorded['first_rejection_reason_census'], 'Fusion first-failure census differs')
    require(census == Counter({'fuel_exhausted': 132389, 'symbolic_abstraction_limit': 15336,
                              'unexpected_halt': 643}), 'Recorded failure reasons differ')
    require(not recorded['affine_survivors'] and not recorded['bootstrap_survivors'], 'Unexpected recorded survivor')
    return {'recorded_candidates': len(rows), 'first_rejection_reason_census': dict(census),
            'full_search_repeated': False,
            'scope': 'Ledger integrity only; timeouts and abstraction limits remain unresolved.'}


def full_search(scratch):
    out = scratch / 'full-search'
    run_python(HERE / 'measure_fixedpoint.py', ['--repo', REPO, '--out', out, '--seeds', '64'])
    actual = read_json(out / 'results.json')
    expected = read_json(HERE / 'fixedpoint/results.json')
    actual.pop('elapsed_seconds', None)
    expected.pop('elapsed_seconds', None)
    require(actual == expected, 'Full-search aggregate differs from the supplied record')
    for mode in SELECTED:
        require((out / mode / 'winner_total.tm').read_bytes() == (HERE / 'fixedpoint' / mode / 'winner_total.tm').read_bytes(),
                'Full-search winner differs')
    return {'selected_candidates_compiled': sum(row['selected_family_cases'] for row in actual['results']),
            'all_ten_distributions_and_recipes_match': True, 'selected_literal_winners_match': True}


def fusion_search(scratch):
    out = scratch / 'fusion-search'
    run_python(HERE / 'lab/fuse_states.py', ['--repo', REPO, '--out', out])
    actual = read_json(out / 'fusion_results.json')
    expected = read_json(HERE / 'fusion/fusion_results.json')
    for obj in (actual, expected):
        obj.pop('elapsed_seconds', None)
        obj.pop('ledger_sha256', None)  # gzip headers contain generation time
    require(actual == expected, 'Fusion logical result differs from the supplied record')
    require(gzip.decompress((out / 'rejection_ledger.csv.gz').read_bytes()) ==
            gzip.decompress((HERE / 'fusion/rejection_ledger.csv.gz').read_bytes()),
            'Uncompressed candidate ledger differs')
    return {'tested': actual['tested'], 'fuel': actual['fuel'],
            'first_rejection_reason_census': actual['first_rejection_reason_census'],
            'uncompressed_candidate_ledger_matches': True, 'full_search_repeated': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='Run the quick checks (also the default).')
    parser.add_argument('--full-search', action='store_true', help='Additionally recompile all 20,480 selected candidates.')
    parser.add_argument('--fusion', action='store_true', help='Additionally repeat the bounded fusion search.')
    parser.add_argument('--output', type=Path, help='Optional JSON verification report path.')
    args = parser.parse_args()
    require(not sys.flags.optimize, 'Assertions must be enabled; do not use python -O')
    begin = time.monotonic()
    result = {'pinned_inputs': check_sources(), 'python': sys.version.split()[0],
              'offline': True, 'dependencies': 'Python standard library and supplied source files only',
              'compiler_and_calculus_formalized': False, 'new_ConZFC_machine_claimed': False}
    audit = load('engineering_audit', RESEARCH / 'audit_tm.py')
    result['baseline253'] = baseline_check(audit)
    result['recorded_fusion_ledger'] = check_recorded_fusion()
    with tempfile.TemporaryDirectory(prefix='zfc-engineering-replay-') as temp:
        scratch = Path(temp)
        result['controls'] = check_controls(scratch, audit)
        if args.full_search:
            result['full_search'] = full_search(scratch)
        if args.fusion:
            result['fusion_search'] = fusion_search(scratch)
    result['elapsed_seconds'] = time.monotonic() - begin
    result['status'] = 'PASS'
    if args.output:
        write_json(args.output, result)
    print(json.dumps({'status': result['status'], 'pinned_files': result['pinned_inputs']['pinned_files_verified'],
                     'controls': [{'mode': row['mode'], 'states': row['working_states'],
                                   'related_operation_pairs': row['independent_operation_check']['related_operation_pairs'],
                                   'successor_pairs': row['independent_operation_check']['successor_pairs_verified']}
                                  for row in result['controls']],
                     'baseline253_bootstrap_steps': result['baseline253']['bootstrap_steps'],
                     'fusion_census': result['recorded_fusion_ledger']['first_rejection_reason_census'],
                     'full_search_repeated': args.full_search, 'fusion_search_repeated': args.fusion,
                     'elapsed_seconds': round(result['elapsed_seconds'], 3)}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, AssertionError, OSError) as error:
        print(f'REPRODUCTION FAIL: {error}', file=sys.stderr)
        raise SystemExit(1)
