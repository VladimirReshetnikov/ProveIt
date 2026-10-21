#!/usr/bin/env python3
"""Portable quick audit of the frozen research packet (Python 3 standard library).

This checks file identities, source structure/CFGs, certificate bookkeeping,
complete blank traces, and the exact local marker proof. It does not replace
replay_full_runtime.py or claim that bounded tests prove arbitrary-value runtime.
"""
from pathlib import Path
import argparse, gzip, hashlib, importlib.util, json, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'baseline/k215'
VERIFIED = ROOT / 'verified-machines'
PIN = '2762b8a183830b1f5a30cf059ffb4d92e77cddde'
PARENT_SHA = '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
SOURCE_SHA = '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
CB_SHA = 'c6ff22b5446bb7f14a9f8ea02828fa694291ce1b7c71cf1ea3cb488d03d30dc5'
NORMAL_SHA = '04a920b972cd14da6d9bb0496a31fb882f2a37be9dae333894301c290176df7c'
NEW_SOURCE_SHA = '79425cf76b24b8739fd00e3fd091ca00de3b3379324f941158ba5e58061dc2b0'
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    if str(path).endswith('.gz'):
        with gzip.open(path, 'rt', encoding='utf-8') as stream:
            return json.load(stream)
    return json.loads(Path(path).read_text())


def table(path):
    result = {}
    for line in Path(path).read_text().splitlines():
        a = line.split()
        if len(a) == 5 and a[3] in ('L', 'R') and all(a[i].isdigit() for i in (0, 1, 2, 4)):
            q, b, w, z = (int(a[i]) for i in (0, 1, 2, 4))
            assert b in (0, 1) and w in (0, 1) and (q, b) not in result
            result[q, b] = (w, 1 if a[3] == 'R' else -1, z)
    states = {q for q, b in result}
    assert len(states) == 215 and len(result) == 430
    assert all((q, b) in result for q in states for b in (0, 1))
    assert {z for w, d, z in result.values()} - states == {254}
    seen = {0}
    todo = [0]
    while todo:
        q = todo.pop()
        if q == 254:
            continue
        for b in (0, 1):
            z = result[q, b][2]
            if z not in seen:
                seen.add(z)
                todo.append(z)
    assert seen - {254} == states
    return result


def blank_trace(t, saved):
    q = h = 0
    ones = set()
    trace = saved['trace']
    assert len(trace) == saved['steps']
    for actual in trace:
        b = int(h in ones)
        w, d, z = t[q, b]
        assert actual == [q, h, b, w, d, z]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        q, h = z, h + d
    assert (q, h) == (saved['state'], saved['head'])
    assert sorted(ones) == saved['one_cells']
    assert q == 84 and h == -12 and saved['gap'] == 5
    assert saved['registers'] == [5, 0, 0, 0, 0, 0, 0, 0, 4]
    assert saved['spares'] == [1] * 45
    # Independently reconstruct the whole canonical root frame. Blank initial
    # tape and exact finite updates ensure there are no hidden exterior ones.
    header = h + 64 + saved['gap']
    want = {h - 1, header}
    values = [0] * 9
    for i, j in enumerate(PHY):
        values[j] = saved['registers'][i]
    cursor = header + 1
    for value in values + saved['spares']:
        want.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    assert ones == want
    assert all(step[0] != 13 for step in trace[:3])
    return {'steps': len(trace), 'state': q, 'head': h, 'gap': saved['gap'],
            'registers': saved['registers'], 'spare_count': 45,
            'one_cells': len(ones), 'whole_zero_exterior_checked': True}


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-manifest', action='store_true')
    args = parser.parse_args()
    assert sha(BASE / 'k215.native.tm') == PARENT_SHA
    assert sha(BASE / 'sites215.json') == SOURCE_SHA
    assert sha(VERIFIED / 'q13_cb215.native.tm') == CB_SHA
    assert sha(VERIFIED / 'q13_normal215.native.tm') == NORMAL_SHA
    assert sha(VERIFIED / 'q13_cb.sites.json') == NEW_SOURCE_SHA
    parent = table(BASE / 'k215.native.tm')
    cb = table(VERIFIED / 'q13_cb215.native.tm')
    normal = table(VERIFIED / 'q13_normal215.native.tm')
    expected = dict(parent)
    expected[8, 1] = (1, 1, 103)
    assert cb == expected
    expected[13, 0] = (0, 1, 49)
    expected[13, 1] = (0, 1, 60)
    assert normal == expected

    sys.path.insert(0, str(BASE / 'code'))
    import source_language as source
    old_rows = read_json(BASE / 'sites215.json')
    new_rows = read_json(VERIFIED / 'q13_cb.sites.json')
    old = source.tree(old_rows)
    left, body = old
    gate, rest = left
    transfer, rest = rest
    increment, restore = rest
    rebuilt = ((gate, (transfer, (increment, (restore, ('CB', 1))))), body)
    assert [list(x) for x in source.sites(rebuilt)] == new_rows
    new_metrics = source.metrics(rebuilt)
    assert list(new_metrics.values()) == [202, 4752, 47, 6]

    histories = load_module(ROOT / 'formalism/history_markers.py', 'marker_histories')
    for t in (cb, normal):
        for b in (0, 1):
            cert = histories.histories(t, 13, b, 3)
            assert cert['feasible_histories'] > 0
            assert cert['common_cells'][-1] == 0 and cert['common_cells'][-2] == 1
    for b, endpoint in ((0, 49), (1, 60)):
        cells = {-1: 0, 0: b}
        q = 13
        h = 0
        for _ in range(3):
            assert h in cells, 'local block read outside its quantified footprint'
            w, d, z = cb[q, cells[h]]
            cells[h] = w
            q, h = z, h + d
        assert (q, h, cells) == (endpoint, 1, {-1: 0, 0: 0})
        assert normal[13, b] == (0, 1, endpoint)

    runtime = {}
    expected_cases = [(i, positive) for i, (_, op, arg) in enumerate(new_rows)
                      for positive in ((False, True) if op == 'CD' else (False,))]
    assert len(expected_cases) == 6177
    for name, t, digest, expected_steps in (
        ('q13_cb215_check', cb, CB_SHA, 88116),
        ('q13_normal215_check', normal, NORMAL_SHA, 87920),
    ):
        d = VERIFIED / name
        receipt = read_json(d / 'runtime.json')
        cases = read_json(d / 'runtime_cases.json.gz')
        assert receipt['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
        assert receipt['table_sha256'] == digest and receipt['sites_sha256'] == NEW_SOURCE_SHA
        assert receipt['checker_sha256'] == sha(BASE / 'code/runtime-inputs/runtime/symbolic_runtime.py')
        assert receipt['helper_sha256'] == sha(BASE / 'code/runtime-inputs/runtime/independent_runtime.py')
        assert receipt['expected_cases'] == receipt['proved_cases'] == 6177
        assert not receipt['failures'] and len(receipt['blocks']) == 4
        assert [(c['site_index'], c['positive']) for c in cases] == expected_cases
        assert all(c['duration'][0] > 0 and all(v >= 0 for v in c['duration'][1:]) for c in cases)
        startup = blank_trace(t, read_json(d / 'startup.json.gz'))
        assert startup['steps'] == expected_steps
        runtime[name] = {'states': 215, 'guarded_cases': len(cases),
                         'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
                         'minimum_duration_constant': min(c['duration'][0] for c in cases),
                         'startup': startup}

    base_graph = source.graph_intervals(old_rows)
    checked = 0
    for directory in ('open-results', 'zero-anneal-52'):
        for path in sorted((ROOT / 'source-reassociation' / directory).glob('candidate*.json')):
            if '-recipe' in path.name:
                continue
            rows = read_json(path)
            assert len(rows) == len(old_rows)
            assert [(op, a) for _, op, a in rows if op not in ('CB', 'CC')] == [
                (op, a) for _, op, a in old_rows if op not in ('CB', 'CC')]
            assert source.graph_intervals(rows) == base_graph
            assert source.graph_arithmetic(rows)[0] == base_graph
            assert source.metrics(source.tree(rows))['dag_nodes'] == 202
            checked += 1
    assert checked == 170

    binder_minima = {}
    for name, minimum in [('G_I', 203), ('G_Q', 202), ('G_E', 204), ('G_sumAB1a', 204)]:
        directory = ROOT / 'new-binder-search' / name
        summary = read_json(directory / 'row_permutation_exact_summary.json')
        assert summary['total_vectors'] == 279936 and summary['best'] == minimum
        assert len(summary['results']) == 4
        for record in summary['results']:
            assert source.metrics(source.tree(read_json(directory / record['file'])))['dag_nodes'] == minimum
        binder_minima[name] = minimum

    # Re-run the exact polynomial/finite-support certificate and the independent
    # scheduler source audit, writing only into a private temporary directory.
    with tempfile.TemporaryDirectory(prefix='zfc-quick-audit-', dir=ROOT.parent) as scratch:
        scratch = Path(scratch)
        subprocess.run([sys.executable, str(ROOT / 'formalism/check_binders.py'), '--output',
                        str(scratch / 'binders.json')], check=True, capture_output=True, text=True)
        assert read_json(scratch / 'binders.json') == read_json(ROOT / 'formalism/binder_certificate.json')
        subprocess.run([sys.executable, str(ROOT / 'formalism/check_refill_source.py'),
                        str(BASE / 'sites215.json'), str(VERIFIED / 'q13_cb.sites.json'),
                        '--output', str(scratch / 'refill.json')], check=True, capture_output=True, text=True)
        refill = read_json(scratch / 'refill.json')
        assert refill['status'] == 'EXACT_SOURCE_PREMISES_PASS'
        assert refill['actual_seed_reduction']['source_steps'] == 65

    manifest_count = None
    if not args.skip_manifest and (ROOT / 'MANIFEST.json').exists():
        manifest = read_json(ROOT / 'MANIFEST.json')
        for item in manifest['files']:
            path = ROOT / item['path']
            assert path.is_file() and path.stat().st_size == item['bytes']
            assert sha(path) == item['sha256'], item['path']
        manifest_count = len(manifest['files'])
    result = {'status': 'QUICK_ARCHIVE_AUDIT_PASS', 'parent_commit': PIN,
              'accepted_new_state_count': 215, 'accepted_214_or_fewer': False,
              'new_source_metrics': new_metrics, 'verified_machines': runtime,
              'source_reassociations_checked': checked, 'binder_family_minima': binder_minima,
              'binder_certificate_replayed': True, 'refill_source_audit_replayed': True,
              'exact_marker_and_three_step_blocks_checked': True,
              'manifest_files_checked': manifest_count,
              'scope': 'Identity, exact finite structure, whole blank traces, local all-tape blocks, and receipt bookkeeping. Use replay_full_runtime.py for fresh arbitrary-value primitive proofs.'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
