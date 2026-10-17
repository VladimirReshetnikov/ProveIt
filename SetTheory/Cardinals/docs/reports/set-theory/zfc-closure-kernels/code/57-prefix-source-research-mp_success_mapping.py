#!/usr/bin/env python3
"""Replay the single successful-MP continuation mapping on pinned repository data.

All 8,366 changed-program guards use the four unchanged register-box contracts.
The separate one-million-step blank diagnostic proves no nonhalting/calibration
result. No repository source/table is edited and no proof/compiler build is run.
Original program/framework attribution: Mira-Cult, Jeff and Wade; upstream pin
297ab8df7e5de329605c3875b4934643b371a5e3. Public253 and the frozen selector
permutation remain attributed as in candidate252_independent_audit.py.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib.util
import json
import sys
import time
import types

sys.dont_write_bytecode = True
PREFIX = 'Computability/BusyBeaver/'
PINNED = {
    'table': (PREFIX+'Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm', '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'),
    'bisim254': (PREFIX+'Research/ZFC/bisim254.py', 'ff575f4d728333f0ebd1a4236014d13169b2eda081c5bc10f4d23be5d858958e'),
    'candidate_audit': (PREFIX+'Research/ZFC/candidate252_independent_audit.py', '470748041060df0b2dbd4704934f897785b61c2dc11a10f3ade73284d6f63be3'),
    'Prog254': (PREFIX+'Lean/BusyBeaver/ZFC/Prog254.lean', '6e564bd1ba179b2d39fccc3b8c86a681ec0dd6529df9cfa2522500eef140cfde'),
    'Dag254': (PREFIX+'Lean/BusyBeaver/ZFC/Dag254.lean', 'e42a8658265b114a99f3550f979b95f1afc02a2f7d6483e1765d911891c05f52'),
    'strict': ('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py', 'da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce'),
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def save(path, value, compact=False):
    if compact:
        text = json.dumps(value, separators=(',', ':'))
    else:
        text = json.dumps(value, indent=2)
    path.write_text(text+'\n', encoding='utf-8')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions must remain enabled; do not use Python -O.')
    repo, output = args.repo.resolve(), args.output.resolve()
    if not repo.is_dir():
        ap.error('--repo must be an existing repository directory.')
    if output.is_relative_to(repo):
        ap.error('--output must be outside the repository.')
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        ap.error('--output must be absent or empty.')
    inputs = []
    for role, (relative, expected) in PINNED.items():
        path = repo/relative
        actual = sha(path)
        if actual != expected:
            ap.error(f'{role} input hash mismatch: {path}')
        inputs.append(dict(role=role, repo_path=relative, path=str(path), sha256=actual))
    inputs.append(dict(role='driver', path=str(Path(__file__).resolve()), sha256=sha(__file__)))
    output.mkdir(parents=True, exist_ok=True)
    paths = {row['role']: Path(row['path']) for row in inputs}
    record = dict(status='FAILED', scope=__doc__, repo=str(repo),
                  command=[sys.executable, *sys.argv], python_version=sys.version,
                  input_files=inputs, lean_build=False, compiler_build=False,
                  output_directory=str(output))
    try:
        bi = load('mp_mapping_bisim', paths['bisim254'])
        au = load('mp_mapping_candidate', paths['candidate_audit'])
        sys.modules['cost_search'] = types.SimpleNamespace()
        st = load('mp_mapping_strict', paths['strict'])
        raw = paths['table'].read_bytes()
        base = au.read_table(raw)
        assert sha(paths['table']) == au.EXPECTED_SHA
        table = {(str(q), b): (v, d, str(t)) for (q, b), (v, d, t) in base.items()}
        changed = dict(table)
        assert changed['204', 1] == (1, 'R', '113')
        changed['204', 1] = (1, 'R', '132')
        assert len(au.BOX_PAIRS) == 55
        assert all(changed[str(q), b] == table[str(q), b] for q, b in au.BOX_PAIRS)
        prog, dag = bi.load_prog254(), bi.load_dag254()
        assert prog[6423][1] == ('node', 6434)
        assert prog[6434] == (('node', 6435), ('node', 6453))
        assert dag[130][1] == ('node', 166)
        newp, newd = list(prog), list(dag)
        newp[6423] = (newp[6423][0], ('node', 6453))
        newd[130] = (newd[130][0], ('node', 167))
        relations = bi.build(bi.Prog(newp), bi.Prog(newd))
        assert len(relations) == 2998
        artifacts = {}
        for role, name, value in [
            ('modified_literal_rows', 'modified-Prog254-rows.json', newp),
            ('modified_dag_rows', 'modified-Dag254-rows.json', newd),
            ('segment_certificate', 'modified-segment-certificate.json', relations),
        ]:
            save(output/name, value, compact=True)
            artifacts[role] = dict(file=name, sha256=sha(output/name))
        sites = []

        def walk(node, prefix):
            for bit, edge in enumerate(newp[node]):
                path = prefix+str(bit)
                if edge[0] == 'node':
                    walk(edge[1], path)
                else:
                    sites.append((path, edge[0], edge[1]))

        walk(0, '')
        assert len(sites) == 6441
        start = time.monotonic()
        failures, checks, totals = [], 0, Counter()
        for path, op, register in sites:
            for zero in ((True, False) if op == 'decnz' else (None,)):
                operation = {'inc':'CI', 'decnz':'CD', 'brk':'CB', 'cont':'CC', 'halt':'CH'}[op]
                physical = au.NEWPHYS[register] if op in ('inc', 'decnz') else register
                branch = (physical, zero) if op == 'decnz' else None
                pc = au.successor(path, operation, register, zero)
                effect = ('inc', physical) if op == 'inc' else ('dec', physical) if op == 'decnz' and not zero else None
                right = [('b', int(c)) for c in pc] if pc is not None else []
                right += [('r', 0, 1, (41 if pc is None else 40)-len(pc or '')), ('b', 1), ('box', ('plain', effect))]
                try:
                    rules, literal = st.run(changed, path, branch, st.canon([('b', 1)], right), halt=op == 'halt', fuel=1000)
                    assert literal > 0
                    totals.update(rules)
                except (AssertionError, KeyError) as ex:
                    failures.append(dict(case=checks, path=path, op=op, arg=register, zero=zero, error=str(ex)))
                checks += 1
        assert checks == 8366
        symbolic_seconds = time.monotonic()-start
        spares = [0]*65
        spares[8] = 1
        target = au.paint('', 40, [0]*9, spares, 2)
        numeric = {(int(q), b): (v, d, int(t)) for (q, b), (v, d, t) in changed.items()}
        q, head, ones = 64, 0, set()
        first_target = halt = None
        used = Counter()
        limit = 1000000
        blank_start = time.monotonic()
        for i in range(limit+1):
            if (q, head, ones) == (96, 2, target):
                first_target = i
                break
            if q == 254:
                halt = i
                break
            if i == limit:
                break
            key = q, int(head in ones)
            used[key] += 1
            write, move, q = numeric[key]
            if write:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if move == 'R' else -1
        record.update(
            status='DIAGNOSTIC_COMPLETE', artifacts=artifacts,
            upstream_commit='297ab8df7e5de329605c3875b4934643b371a5e3',
            patch=dict(literal_program_node=6423, right_edge_before=['node',6434], right_edge_after=['node',6453], dag_node=130, right_after=['node',167], old_label_binary_row=[204,1], old_action=[1,'R',113], new_action=[1,'R',132]),
            new_source=dict(segment_relation_pairs=len(relations), instruction_sites=len(sites), guard_cases=checks),
            conditional_symbolic=dict(fuel=1000, passed=checks-len(failures), failures=failures, symbolic_seconds=symbolic_seconds, rule_totals=dict(totals), protected_box_rows_unchanged=True, contracts='Exactly the four attributed unchanged register-box contracts; no new Lean runtime proof.'),
            blank_control=dict(limit=limit, first_exact_original_whole_boot_frame=first_target, halt=halt, last_step=i, last_state=q, last_head=head, last_ones_count=len(ones), patch_row_visits=used[204,1], blank_seconds=time.monotonic()-blank_start),
            working_states=len({q for q, _ in changed}), transition_rows=len(changed),
            logical_to_physical=list(au.NEWPHYS),
            changed_table_sha256=hashlib.sha256(au.encode(numeric)).hexdigest())
        assert not failures, 'conditional checker rejection; inspect failures, not a mathematical counterexample'
        for item in inputs:
            assert sha(item['path']) == item['sha256'], ('input changed during replay', item['path'])
        for item in artifacts.values():
            assert sha(output/item['file']) == item['sha256']
        record['input_postchecks_passed'] = True
        record['frozen_inputs_unchanged'] = True
        save(output/'results.json', record)
        print(json.dumps(dict(status=record['status'], output=str(output), source=record['new_source'], conditional_passed=checks, blank_control=record['blank_control']), indent=2))
    except BaseException as ex:
        record['status'] = 'FAILED'
        record['error'] = f'{type(ex).__name__}: {ex}'
        save(output/'results.json', record)
        raise


if __name__ == '__main__':
    main()
