#!/usr/bin/env python3
"""Read mapping output, then replay finite MP graph and whole-tape root controls.

This is a bounded diagnostic, not a runtime/calibration or state lower-bound
proof. Both source data and the frozen252 table remain unchanged. The three
changed-source artifacts come from the separately recorded mapping replay.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import importlib.util
import json
import sys
import time

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


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--mapping-output', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        ap.error('Assertions must remain enabled; do not use Python -O.')
    repo, mapping, output = args.repo.resolve(), args.mapping_output.resolve(), args.output.resolve()
    if not repo.is_dir() or not mapping.is_dir():
        ap.error('--repo and --mapping-output must be existing directories.')
    if output.is_relative_to(repo) or output == mapping:
        ap.error('--output must be outside the repository and distinct from mapping output.')
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        ap.error('--output must be absent or empty.')
    inputs = []
    for role, (relative, expected) in PINNED.items():
        path = repo/relative
        if sha(path) != expected:
            ap.error(f'{role} input hash mismatch: {path}')
        inputs.append(dict(role=role, repo_path=relative, path=str(path), sha256=expected))
    report_path = mapping/'results.json'
    report = json.loads(report_path.read_text(encoding='utf-8'))
    assert report['status'] == 'DIAGNOSTIC_COMPLETE'
    assert report['new_source'] == dict(segment_relation_pairs=2998, instruction_sites=6441, guard_cases=8366)
    assert report['conditional_symbolic']['passed'] == 8366 and report['conditional_symbolic']['failures'] == []
    assert report['input_postchecks_passed'] and report['frozen_inputs_unchanged']
    mapping_inputs = {row['role']: row for row in report['input_files']}
    for role, (relative, expected) in PINNED.items():
        assert mapping_inputs[role]['repo_path'] == relative
        assert mapping_inputs[role]['sha256'] == expected
    mapping_driver = Path(__file__).resolve().with_name('mp_success_mapping.py')
    assert sha(mapping_driver) == mapping_inputs['driver']['sha256']
    inputs += [dict(role='mapping_driver', path=str(mapping_driver), sha256=sha(mapping_driver)),
               dict(role='mapping_report', path=str(report_path), sha256=sha(report_path)),
               dict(role='driver', path=str(Path(__file__).resolve()), sha256=sha(__file__))]
    expected_artifact_names = dict(modified_literal_rows='modified-Prog254-rows.json', modified_dag_rows='modified-Dag254-rows.json', segment_certificate='modified-segment-certificate.json')
    artifacts = {}
    for role, name in expected_artifact_names.items():
        item = report['artifacts'][role]
        assert item['file'] == name
        path = mapping/name
        assert sha(path) == item['sha256']
        inputs.append(dict(role=role, path=str(path), sha256=item['sha256']))
        artifacts[role] = dict(mapping_file=name, sha256=item['sha256'])
    output.mkdir(parents=True, exist_ok=True)
    record = dict(status='FAILED', scope=__doc__, repo=str(repo), mapping_output=str(mapping),
                  command=[sys.executable, *sys.argv], python_version=sys.version,
                  input_files=inputs, artifacts=artifacts, lean_build=False, compiler_build=False)

    def save():
        (output/'structure-and-boot.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')

    try:
        paths = {row['role']: Path(row['path']) for row in inputs}
        bi = load('mp_structure_bisim', paths['bisim254'])
        au = load('mp_structure_candidate', paths['candidate_audit'])
        p = json.loads(paths['modified_literal_rows'].read_text())
        d = json.loads(paths['modified_dag_rows'].read_text())
        cert = json.loads(paths['segment_certificate'].read_text())
        original_p = json.loads(json.dumps(bi.load_prog254()))
        original_d = json.loads(json.dumps(bi.load_dag254()))
        assert len(p) == 6459 and len(d) == 219 and len(cert) == 2998
        assert [(i,b,original_p[i][b],p[i][b]) for i in range(len(p)) for b in (0,1) if original_p[i][b] != p[i][b]] == [(6423,1,['node',6434],['node',6453])]
        assert [(i,b,original_d[i][b],d[i][b]) for i in range(len(d)) for b in (0,1) if original_d[i][b] != d[i][b]] == [(130,1,['node',166],['node',167])]
        table = au.read_table(paths['table'].read_bytes())
        baseline = dict(table)
        assert table[204,1] == (1,'R',113)
        table[204,1] = (1,'R',132)
        assert hashlib.sha256(au.encode(table)).hexdigest() == report['changed_table_sha256']
        assert all(table[key] == baseline[key] for key in au.BOX_PAIRS)
        states = {q for q, _ in table}
        seen, todo = set(), [64]
        while todo:
            q = todo.pop()
            if q == 254 or q in seen:
                continue
            seen.add(q)
            todo.extend(table[q,b][2] for b in (0,1))
        partition = {q:0 for q in states}
        partition[254] = -1
        iterations = 0
        while True:
            signatures = {q:tuple((table[q,b][0],table[q,b][1],partition[table[q,b][2]]) for b in (0,1)) for q in states}
            ids = {value:i for i,value in enumerate(sorted(set(signatures.values())))}
            new = {q:ids[value] for q,value in signatures.items()}
            new[254] = -1
            iterations += 1
            if all((partition[a] == partition[b]) == (new[a] == new[b]) for a in states for b in states):
                partition = new
                break
            partition = new
        classes = defaultdict(list)
        for q in sorted(states):
            classes[partition[q]].append(q)
        q, chain = 96, []
        for bit in '111111':
            action = table[q,int(bit)]
            chain.append(dict(state=q, read=int(bit), action=action))
            assert action[:2] == (int(bit),'R')
            q = action[2]
        assert q == 132

        def parse(q, head, ones):
            if q != 96 or head-1 not in ones or any(x < head-1 for x in ones):
                return None
            right = sorted(x for x in ones if x >= head)
            if not right:
                return None
            gap = right[0]-head
            if gap < 40:
                return None
            cursor, last, values = right[0]+1, max(ones), []
            while cursor <= last:
                if cursor in ones or cursor+1 not in ones:
                    return None
                cursor += 1
                count = 0
                while cursor in ones:
                    count += 1
                    cursor += 1
                values.append(count-1)
            if len(values) < 9:
                return None
            assert ones == au.paint('',gap,values[:9],values[9:],head)
            return dict(head=head, gap=gap, primary=values[:9], spares=values[9:], whole_ones_count=len(ones))

        start = time.monotonic()
        q, head, ones, roots = 64, 0, set(), []
        limit = 1000000
        for time_index in range(limit+1):
            frame = parse(q,head,ones)
            if frame is not None:
                frame.update(time=time_index)
                roots.append(frame)
                if len(roots) == 20:
                    break
            if q == 254 or time_index == limit:
                break
            write, move, q = table[q,int(head in ones)]
            if write:
                ones.add(head)
            else:
                ones.discard(head)
            head += 1 if move == 'R' else -1
        qb, hb, ob, baseline_first = 64, 0, set(), None
        for bt in range(82553):
            frame = parse(qb,hb,ob)
            if frame is not None:
                baseline_first = dict(time=bt, **frame)
                break
            if bt == 82552:
                break
            write, move, qb = baseline[qb,int(hb in ob)]
            if write:
                ob.add(hb)
            else:
                ob.discard(hb)
            hb += 1 if move == 'R' else -1
        assert baseline_first is not None
        assert baseline_first['time'] == 82552 and baseline_first['head'] == 2 and baseline_first['gap'] == 40
        assert baseline_first['primary'] == [0]*9 and baseline_first['spares'] == [0]*8+[1]+[0]*56
        record.update(status='DIAGNOSTIC_COMPLETE', working_states=len(states), syntactic_reachable_from_start=len(seen), unreachable=sorted(states-seen), exact_step_bisimulation_iterations=iterations, exact_step_bisimulation_nontrivial_classes=[value for value in classes.values() if len(value)>1], dispatch_MP_chain=chain,
                      incoming_shared113=[dict(row=key,action=action) for key,action in sorted(table.items()) if action[2] == 113], incoming_copy132=[dict(row=key,action=action) for key,action in sorted(table.items()) if action[2] == 132],
                      matching_original_whole_root_control=baseline_first,
                      bounded_whole_tape_roots=dict(limit=limit,roots=roots,last_step=time_index,last_state=q,last_head=head,last_ones_count=len(ones)), diagnostic_seconds=time.monotonic()-start,
                      limits=['Syntactic reachability treats both input bits freely.','The parser requires sufficient gap≥40 and exact complete tape; no stronger dirty-start exclusion follows.','No observed root/halt within fuel proves neither nonhalting nor failure of every initializer.','Singleton strong exact-step classes are not a general minimality theorem.','No table was emitted or baseline file mutated.'])
        for item in inputs:
            assert sha(item['path']) == item['sha256'], ('input changed during replay',item['path'])
        record['input_postchecks_passed'] = True
        save()
        print(json.dumps(dict(status=record['status'],output=str(output),working_states=len(states),reachable=len(seen),strong_bisim_nontrivial_classes=record['exact_step_bisimulation_nontrivial_classes'],modified_roots=record['bounded_whole_tape_roots'],baseline_time=baseline_first['time']),indent=2))
    except BaseException as ex:
        record['status'] = 'FAILED'
        record['error'] = f'{type(ex).__name__}: {ex}'
        save()
        raise


if __name__ == '__main__':
    main()
