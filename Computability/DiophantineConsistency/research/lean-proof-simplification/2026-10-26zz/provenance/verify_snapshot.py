#!/usr/bin/env python3
"""Portable offline source provenance replay. No Lean, network, or assert statements.

This verifies bundled evidence against saved GitHub receipts; it does not authenticate
GitHub independently, elaborate Lean, or claim a complete dependency checkout.
"""
import hashlib
import json
import pathlib
import sys

BASE = pathlib.Path(__file__).resolve().parents[1]
P = BASE / 'provenance'
PIN = '7ba7d102822df1eff376cbca913727d9d588ab4e'
PREVIOUS = '9d9d1123b39927d30363f1dcd53c23f0575c30ee'
PREVIOUS_CLOSING = '451b548a198c791e81abc40435979c89edb40b23'
PRE = 'Computability/DiophantineConsistency/Lean/'
FAILURES = []
COUNTS = {}

def check(ok, message):
    if not ok:
        FAILURES.append(message)

def read(name):
    return json.loads((P / name).read_text(encoding='utf-8'))

def safe_local(name):
    path = BASE / name
    if path.is_symlink() or not path.resolve().is_relative_to(BASE.resolve()):
        raise ValueError('unsafe artifact path: ' + name)
    return path

def gitsha(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def treehash(rows):
    ordered = sorted(rows, key=lambda e: (e['path'] + ('/' if e['type'] == 'tree' else '')).encode())
    data = b''.join((e['mode'].lstrip('0') + ' ' + e['path']).encode() + b'\0' + bytes.fromhex(e['sha']) for e in ordered)
    return gitsha('tree', data)

def blobmap(tree, prefix):
    return {prefix + e['path']: e['sha'] for e in tree['tree'] if e['type'] == 'blob'}

def source_tree_names():
    names = ['root_tree', 'computability_tree', 'dc_root_tree', 'Lean_tree', 'reviews_tree',
             'audit_research_root_tree', 'audit_proposals_tree', 'Logic_tree', 'FirstOrder_tree',
             'FirstOrder_Lean_root_tree', 'FirstOrder_modules_tree', 'SetTheory_tree',
             'BoundedConsistency_tree', 'BoundedConsistency_Lean_root_tree', 'BoundedZFC_tree',
             'HilbertTenthProblem_tree', 'H10_Lean_tree', 'BusyBeaver_tree',
             'BusyBeaver_Lean_root_tree', 'BusyBeaver_modules_tree', 'BusyBeaver_ZFC_tree']
    names += [prefix + name for prefix in ['previous_', 'round6_closing_']
              for name in ['root_tree', 'computability_tree', 'dc_root_tree', 'Lean_tree']]
    names += ['closing_screen_' + name for name in ['root_tree', 'computability_tree', 'dc_tree', 'Lean_tree']]
    return names

def main():
    trees = {name: read(name + '.json') for name in source_tree_names()}
    for name, tree in trees.items():
        check(tree.get('truncated') is False, [name, 'tree not explicitly complete'])
        rows = tree['tree']
        check(len({e['path'] for e in rows}) == len(rows), [name, 'duplicate tree paths'])
        dirs = {'': []}
        entries = {e['path']: e for e in rows}
        for e in rows:
            check(e['type'] in ['tree', 'blob', 'commit'], [name, e['path'], 'unexpected Git type'])
            check(not e['path'].startswith('/') and '..' not in pathlib.PurePosixPath(e['path']).parts,
                  [name, 'unsafe Git path'])
            parent, _, leaf = e['path'].rpartition('/')
            dirs.setdefault(parent, []).append(dict(e, path=leaf))
        check(treehash(dirs['']) == tree['sha'], [name, 'root Git tree SHA mismatch'])
        for path, children in dirs.items():
            if path:
                check(entries.get(path, {}).get('sha') == treehash(children), [name, path, 'nested Git tree SHA mismatch'])

    def edge(parent, path, child):
        actual = next((e['sha'] for e in trees[parent]['tree'] if e['path'] == path), None)
        check(actual == trees[child]['sha'], [parent, path, child, 'ancestor binding mismatch'])

    for prefix in ['', 'previous_', 'round6_closing_']:
        for a, path, c in [('root_tree', 'Computability', 'computability_tree'),
                           ('computability_tree', 'DiophantineConsistency', 'dc_root_tree'),
                           ('dc_root_tree', 'Lean', 'Lean_tree')]:
            edge(prefix + a, path, prefix + c)
    for a, path, c in [('dc_root_tree', 'reviews', 'reviews_tree'),
                       ('dc_root_tree', 'research', 'audit_research_root_tree'),
                       ('audit_research_root_tree', 'lean-proof-simplification', 'audit_proposals_tree'),
                       ('root_tree', 'Logic', 'Logic_tree'),
                       ('Logic_tree', 'FirstOrder', 'FirstOrder_tree'),
                       ('FirstOrder_tree', 'Lean', 'FirstOrder_Lean_root_tree'),
                       ('FirstOrder_Lean_root_tree', 'FirstOrder', 'FirstOrder_modules_tree'),
                       ('root_tree', 'SetTheory', 'SetTheory_tree'),
                       ('SetTheory_tree', 'BoundedConsistency', 'BoundedConsistency_tree'),
                       ('BoundedConsistency_tree', 'Lean', 'BoundedConsistency_Lean_root_tree'),
                       ('BoundedConsistency_Lean_root_tree', 'BoundedZFCConsistency', 'BoundedZFC_tree'),
                       ('computability_tree', 'HilbertTenthProblem', 'HilbertTenthProblem_tree'),
                       ('HilbertTenthProblem_tree', 'Lean', 'H10_Lean_tree'),
                       ('computability_tree', 'BusyBeaver', 'BusyBeaver_tree'),
                       ('BusyBeaver_tree', 'Lean', 'BusyBeaver_Lean_root_tree'),
                       ('BusyBeaver_Lean_root_tree', 'BusyBeaver', 'BusyBeaver_modules_tree'),
                       ('BusyBeaver_modules_tree', 'ZFC', 'BusyBeaver_ZFC_tree')]:
        edge(a, path, c)

    heads = [(read('HEAD_binding.json'), PIN, 'root_tree'),
             (read('previous_HEAD_binding.json'), PREVIOUS, 'previous_root_tree'),
             (read('round6_closing_HEAD_binding.json'), PREVIOUS_CLOSING, 'round6_closing_root_tree')]
    for head, pin, tree in heads:
        body = head.get('commit', head)
        check(head['sha'] == pin, [tree, 'wrong commit'])
        check(body['tree']['sha'] == trees[tree]['sha'], [tree, 'commit/root binding mismatch'])
    check(read('MAIN_REF_binding.json')['object']['sha'] == PIN, 'saved initial main ref differs from frozen source')
    closing_pin = '3b51c69d42ff99bc420698532af3fe1d1f9bd356'
    closing_head = read('CLOSING_HEAD.json')
    check(closing_head['sha'] == read('CLOSING_MAIN_REF_binding.json')['object']['sha'] == closing_pin,
          'closing ref/commit binding mismatch')
    check(closing_head['tree']['sha'] == trees['closing_screen_root_tree']['sha'], 'closing commit/root mismatch')
    for a, path, c in [('root', 'Computability', 'computability'),
                       ('computability', 'DiophantineConsistency', 'dc'), ('dc', 'Lean', 'Lean')]:
        edge('closing_screen_' + a + '_tree', path, 'closing_screen_' + c + '_tree')
    source_active = blobmap(trees['Lean_tree'], '')
    closing_active = blobmap(trees['closing_screen_Lean_tree'], '')
    target_binding = read('CLOSING_target_binding.json')
    check(target_binding['source_commit'] == PIN and target_binding['closing_commit'] == closing_pin,
          'closing target pins mismatch')
    check({e['path'] for e in target_binding['targets']} == {
        'DiophantineConsistency/NativeOuterSeedConstruction.lean',
        'DiophantineConsistency/SelectiveCoefficientBounds.lean'}, 'closing target coverage mismatch')
    for e in target_binding['targets']:
        check(source_active.get(e['path']) == e['source_blob'], [e['path'], 'closing target source binding mismatch'])
        check(closing_active.get(e['path']) == e['closing_blob'], [e['path'], 'closing target closing binding mismatch'])
        check(e['byte_identical'] is (e['source_blob'] == e['closing_blob']), [e['path'], 'incorrect equality claim'])
    closing_delta = read('CLOSING_active_tree_delta.json')
    actual_closing_delta = {path: (source_active.get(path), closing_active.get(path))
                            for path in source_active.keys() | closing_active.keys()
                            if source_active.get(path) != closing_active.get(path)}
    check(actual_closing_delta == {e['path']: (e['source_blob'], e['closing_blob']) for e in closing_delta['files']},
          'closing complete active-tree delta mismatch')
    check(closing_delta['source_commit'] == PIN and closing_delta['closing_commit'] == closing_pin,
          'closing delta pins mismatch')
    closing_counts = {status: sum(e['status'] == status for e in closing_delta['files'])
                      for status in ['added', 'modified', 'removed']}
    check(closing_counts == closing_delta['counts'], 'closing delta count mismatch')

    mappings = [('root_tree', ''), ('dc_root_tree', 'Computability/DiophantineConsistency/'),
                ('Lean_tree', PRE), ('reviews_tree', 'Computability/DiophantineConsistency/reviews/'),
                ('audit_proposals_tree', 'Computability/DiophantineConsistency/research/lean-proof-simplification/'),
                ('H10_Lean_tree', 'Computability/HilbertTenthProblem/Lean/'),
                ('BusyBeaver_modules_tree', 'Computability/BusyBeaver/Lean/BusyBeaver/'),
                ('BusyBeaver_ZFC_tree', 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'),
                ('BoundedZFC_tree', 'SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/'),
                ('FirstOrder_modules_tree', 'Logic/FirstOrder/Lean/FirstOrder/')]
    bindings = {}
    for tree, prefix in mappings:
        bindings.update(blobmap(trees[tree], prefix))

    manifests = {}
    all_local = set()
    for name, folder, expected_count in [('source_manifest.json', 'sources', 732),
                                         ('dependency_manifest.json', 'dependencies', 29),
                                         ('review_manifest.json', 'provenance/review_sources', 20),
                                         ('comparison_manifest.json', 'comparison_sources', 19)]:
        manifest = read(name)
        rows = manifest['sources']
        manifests[name] = rows
        COUNTS[folder] = len(rows)
        check(len(rows) == expected_count, [name, 'unexpected manifest coverage count'])
        check(len({e['local_path'] for e in rows}) == len(rows), [name, 'duplicate local paths'])
        expected_locals = {e['local_path'] for e in rows}
        actual_locals = {str(f.relative_to(BASE)) for f in (BASE / folder).rglob('*') if f.is_file()}
        check(actual_locals == expected_locals, [name, 'materialized file set differs from manifest'])
        for e in rows:
            local = e['local_path']
            check(local not in all_local, [local, 'duplicate artifact across manifests'])
            all_local.add(local)
            f = safe_local(local)
            if not f.is_file():
                check(False, [local, 'missing'])
                continue
            data = f.read_bytes()
            check(gitsha('blob', data) == e['sha'], [local, 'Git blob SHA mismatch'])
            check(hashlib.sha256(data).hexdigest() == e['sha256'], [local, 'SHA256 mismatch'])
            check(len(data.splitlines()) == e['line_count'], [local, 'physical line count mismatch'])
            if 'size' in e:
                check(len(data) == e['size'], [local, 'size mismatch'])
            if name == 'comparison_manifest.json':
                old_tree = 'previous_Lean_tree' if e['snapshot'] == 'round6_source' else 'round6_closing_Lean_tree'
                expected = blobmap(trees[old_tree], PRE).get(e['path'])
            else:
                check(manifest['commit'] == PIN, [name, 'wrong manifest pin'])
                expected = bindings.get(e['path'])
            check(expected == e['sha'], [local, 'file/tree binding mismatch'])

    active = blobmap(trees['Lean_tree'], PRE)
    materialized = {e['path']: e['sha'] for e in manifests['source_manifest.json'] if e['path'].startswith(PRE)}
    check(active == materialized, 'complete active Lean subtree coverage mismatch')
    check(len(active) == 724, 'wrong active source count')
    for name, old_tree, label, base in [('active_tree_delta.json', 'previous_Lean_tree', 'round6_source', PREVIOUS),
                                       ('since_closing_delta.json', 'round6_closing_Lean_tree', 'round6_closing', PREVIOUS_CLOSING)]:
        before = blobmap(trees[old_tree], '')
        after = blobmap(trees['Lean_tree'], '')
        actual = {path: (before.get(path), after.get(path)) for path in before.keys() | after.keys() if before.get(path) != after.get(path)}
        delta = read(name)
        check(delta['base'] == base and delta['head'] == PIN, [name, 'wrong comparison pins'])
        check(actual == {e['path']: (e['old_sha'], e['new_sha']) for e in delta['files']}, [name, 'complete Git tree delta mismatch'])
        counts = {'added': 0, 'modified': 0, 'removed': 0}
        for e in delta['files']:
            status = 'modified' if e['old_sha'] and e['new_sha'] else ('added' if e['new_sha'] else 'removed')
            counts[status] += 1
            check(e['status'] == status, [name, e['path'], 'wrong delta status'])
            for folder, key in [('comparison_sources/' + label, 'old_lines'), ('sources', 'new_lines')]:
                path = BASE / folder / PRE / e['path']
                lines = len(path.read_bytes().splitlines()) if path.is_file() else 0
                check(lines == e[key], [name, e['path'], key, 'line count mismatch'])
        check(counts == delta['counts'], [name, 'delta aggregate mismatch'])

    history_rows = read('history_compact.json')
    history = {e['sha']: e for e in history_rows}
    check(len(history) == len(history_rows) == 100, 'history coverage or duplicate commits mismatch')
    for head, pin, tree in heads:
        check(history[pin]['tree'] == trees[tree]['sha'], [pin, 'history root tree mismatch'])
        check(history[pin]['parents'] == [{'sha': e['sha']} for e in head['parents']], [pin, 'history parent mismatch'])

    def ancestors(start):
        seen, todo = set(), [start]
        while todo:
            sha = todo.pop()
            if sha in seen:
                continue
            seen.add(sha)
            todo.extend(e['sha'] for e in history.get(sha, {}).get('parents', []))
        return seen

    for filename, cmpname, base in [('commit_timeline.json', 'compare_round6_source.json', PREVIOUS),
                                    ('since_closing_commit_timeline.json', 'compare_round6_closing.json', PREVIOUS_CLOSING)]:
        timeline, compare = read(filename), read(cmpname)
        difference = ancestors(PIN) - ancestors(base)
        check(not (difference - history.keys()), [filename, 'unresolved parent frontier in claimed commit set'])
        check(base in ancestors(PIN), [filename, 'baseline not an ancestor'])
        check(timeline['base'] == compare['base'] == base and timeline['head'] == compare['head'] == PIN, [filename, 'wrong history pins'])
        check(difference == {e['sha'] for e in timeline['commits']}, [filename, 'parent-graph commit membership mismatch'])
        check(len(difference) == timeline['commit_count'] == timeline['ahead_by'] == compare['ahead_by'] == compare['total_commits'], [filename, 'ahead count mismatch'])
        check(compare['behind_by'] == 0 and compare['status'] == 'ahead', [filename, 'unexpected compare relation'])
        for e in timeline['commits']:
            check(history[e['sha']] == e, [filename, e['sha'], 'timeline metadata mismatch'])

    external = set()
    for path in materialized:
        for line in (BASE / 'sources' / path).read_text(encoding='utf-8').splitlines():
            if line.startswith('import '):
                external.update(i for i in line.split()[1:] if not i.startswith(('DiophantineConsistency', 'Mathlib', 'Init')))
    roots = {'BoundedZFCConsistency': 'SetTheory/BoundedConsistency/Lean/',
             'BusyBeaver': 'Computability/BusyBeaver/Lean/',
             'Diophantine': 'Computability/HilbertTenthProblem/Lean/',
             'FirstOrder': 'Logic/FirstOrder/Lean/'}
    required = {roots[m.split('.')[0]] + m.replace('.', '/') + '.lean' for m in external}
    required |= {'Computability/HilbertTenthProblem/Lean/Diophantine/Common/' + n + '.lean'
                 for n in ['Pell', 'PellMod', 'SignInvariantPolynomial']}
    check(required == {e['path'] for e in manifests['dependency_manifest.json']}, 'direct repository imports plus selected support coverage mismatch')
    route = read('candidate_import_route.json')['route']
    for index, e in enumerate(route):
        check(e['local_path'] in all_local, [e['module'], 'import-route file not in verified manifests'])
        imports = [i for line in safe_local(e['local_path']).read_text(encoding='utf-8').splitlines() if line.startswith('import ') for i in line.split()[1:]]
        check(imports == e['imports'], [e['module'], 'import receipt mismatch'])
        if index + 1 < len(route):
            check(route[index + 1]['module'] in imports, [e['module'], 'broken import route'])

    return {'commit': PIN, 'commit_root_tree': trees['root_tree']['sha'],
            'active_Lean_tree': trees['Lean_tree']['sha'], 'checked_tree_snapshots': len(trees),
            'checked_files': COUNTS, 'active_Lean_files': len(active),
            'delta_vs_round6_source': read('active_tree_delta.json')['counts'],
            'delta_vs_round6_closing': read('since_closing_delta.json')['counts'],
            'commits_since_round6_source': read('commit_timeline.json')['commit_count'],
            'commits_since_round6_closing': read('since_closing_commit_timeline.json')['commit_count'],
            'direct_external_repository_imports': len(external),
            'closing_screen_commit': closing_pin,
            'closing_candidate_files_byte_identical': all(e['byte_identical'] for e in target_binding['targets']),
            'closing_active_delta': closing_counts,
            'Lean_elaboration': 'not run; Lean/Lake unavailable and no installation attempted',
            'scope': 'Exact source provenance, selected dependencies and author review bytes; no proof validation, no full Lake checkout, no proposal-novelty verdict'}

if __name__ == '__main__':
    result = {}
    try:
        result = main()
    except Exception as exc:
        FAILURES.append({'exception': type(exc).__name__, 'message': str(exc)})
    result['failures'] = FAILURES
    result['passed'] = not FAILURES
    print(json.dumps(result, indent=2))
    sys.exit(1 if FAILURES else 0)
