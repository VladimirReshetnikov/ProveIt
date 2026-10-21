#!/usr/bin/env python3
"""Independent live Rocq evidence and literal-data audit; no subprocesses or proof execution."""
from pathlib import Path
import argparse
import hashlib
import json
import re


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--build', type=Path, required=True)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__, 'Assertions must be enabled'
    build, repo, output = args.build.resolve(), args.repo.resolve(), args.output.resolve()
    assert not output.exists(), 'Fresh result required'
    before = {}

    def digest(path):
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()

    def bind(path):
        path = Path(path)
        h = digest(path)
        if str(path) in before:
            assert before[str(path)] == h, ('Changed while reading', path)
        before[str(path)] = h
        return h

    def doc(path):
        bind(path)
        return json.loads(Path(path).read_text())

    plan = doc(build / 'plan.json')
    tc = doc(build / 'toolchain.json')
    order, modules = plan['order'], plan['modules']
    assert plan['target'] == 'K215F.CorrectDense215'
    assert len(order) == len(set(order)) == plan['count'] == 237
    assert set(order) == set(modules)
    assert sum(not n.startswith('K215F.') for n in order) == plan['reference_count'] == 195
    position = {n: i for i, n in enumerate(order)}
    closure = set()

    def visit(n):
        if n in closure:
            return
        closure.add(n)
        for d in modules[n]['dependencies']:
            assert position[d] < position[n], ('Not topological', n, d)
            visit(d)

    visit(plan['target'])
    assert closure == set(order)
    manifest = build / 'k230-rocq/manifest.json'
    assert bind(manifest) == plan['reference_manifest_sha256']
    assert 'version 9.1.0' in tc['compiler'] and tc['stdlib'] == '9.0.0'
    flags = plan['flags']
    assert len(flags) % 3 == 0
    assert all(flags[i] == '-Q' for i in range(0, len(flags), 3))
    assert all(Path(flags[i + 1]) == build / 'work' / flags[i + 2]
               for i in range(0, len(flags), 3))
    selected, objects, endpoints = {}, {}, {}
    seconds = 0.0
    for n in order:
        m = modules[n]
        recpath = build / 'records' / (n + '.json')
        rec = doc(recpath)
        assert rec['module'] == n and rec['status'] == 'PASS' and rec['exit_code'] == 0
        assert rec['post_inputs_unchanged'] is True
        src, target, snap = Path(m['source']), Path(m['target']), Path(rec['source_snapshot'])
        assert snap.is_relative_to(build / 'attempts' / n)
        log, obj = snap.parent / 'output.log', target.with_suffix('.vo')
        assert doc(snap.parent / 'record.json') == rec
        h = bind(src)
        assert h == rec['source_sha256'] == bind(target) == bind(snap)
        if not n.startswith('K215F.'):
            assert h == m['expected_reference_sha256']
        assert bind(log) == rec['output_sha256']
        assert bind(obj) == rec['object_sha256']
        expected = {str(src): h}
        for dep in m['dependencies']:
            parent_obj = Path(modules[dep]['target']).with_suffix('.vo')
            expected[str(parent_obj)] = bind(parent_obj)
            assert expected[str(parent_obj)] == selected[dep]['object_sha256']
        assert rec['inputs'] == expected
        compiler = Path(rec['argv'][0])
        assert bind(compiler) == tc['coqc_sha256']
        opts = ['-w', '-deprecated,-notation-overridden']
        if n.startswith('Undecidability.'):
            opts += ['-set', 'Default Proof Using = Type']
        assert rec['argv'] == [str(compiler), *flags, *opts, str(target)]
        if n in ('K215F.Correct215', 'K215F.CorrectDense215'):
            lines = log.read_text().splitlines()
            assert lines == ['Closed under the global context'] * 2
            assert rec['closed_reports'] == 2
            endpoints[n] = {'record_sha256': bind(recpath), 'source_sha256': h,
                            'object_sha256': bind(obj), 'log_sha256': bind(log),
                            'closed_reports': 2}
        selected[n] = {'record_sha256': bind(recpath), 'source_sha256': h,
                       'object_sha256': bind(obj), 'log_sha256': bind(log)}
        objects[str(obj)] = bind(obj)
        seconds += rec['seconds']
    assert len(endpoints) == 2
    kp = build / 'kernel/run1/record.json'
    kernel = doc(kp)
    kl = kp.parent / 'output.log'
    assert kernel['status'] == 'PASS' and kernel['exit_code'] == 0
    assert kernel['post_inputs_unchanged'] is True and kernel['inputs'] == objects
    assert bind(kl) == kernel['output_sha256']
    checker = Path(kernel['argv'][0])
    assert bind(checker) == tc['coqchk_sha256']
    assert kernel['argv'] == [str(checker), *flags, '-silent', '-o', plan['target']]
    assert '-admit' not in kernel['argv'] and '-norec' not in kernel['argv']
    summary = kl.read_text()
    assert '* Theory: Set is predicative' in summary
    assert '* Theory: Rewrite rules are not allowed' in summary
    for label in ['Constants/Inductives relying on type-in-type',
                  'Constants/Inductives relying on unsafe (co)fixpoints',
                  'Inductives whose positivity is assumed']:
        assert '* ' + label + ': <none>' in summary
    utility_axioms = re.findall(r'^    (\S+)$', summary, re.M)
    assert utility_axioms == ['BusyCoq.LibTactics.inj_pair2',
                             'Stdlib.Logic.ProofIrrelevance.proof_irrelevance',
                             'Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq']

    formal = repo / 'Computability/BusyBeaver/Research/ZFC/k225-formal'
    candidate = formal.parent / 'candidate-k215'
    q = formal / 'rocq/rocq-extension/coq/215'
    pins = {'k215.tm': 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
            'k215.native.tm': '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
            'sites215.json': '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'}
    for name, h in pins.items():
        assert bind(candidate / name) == h

    def table(path):
        bind(path)
        result = {}
        for line in path.read_text().splitlines():
            if not line or line.startswith('#'):
                continue
            s, b, w, d, n = line.split()
            key = (int(s), int(b))
            assert key not in result
            result[key] = (int(w), d, int(n))
        return result

    dense, native = table(candidate / 'k215.tm'), table(candidate / 'k215.native.tm')
    assert set(dense) == {(q, b) for q in range(215) for b in (0, 1)}
    assert all(n in range(216) for _, _, n in dense.values())
    rows = re.findall(r'\((true|false), (L|R), (\d+), (true|false), (L|R), (\d+)\)',
                      (q / 'Table215.v').read_text())
    assert len(rows) == 215
    parsed = {(s, b): (int(r[3*b] == 'true'), r[3*b+1], int(r[3*b+2]))
              for s, r in enumerate(rows) for b in (0, 1)}
    assert parsed == dense
    dense_source = (q / 'Dense215.v').read_text()
    label_text = dense_source.split('Definition dense_labels : list nat := [', 1)[1].split(']', 1)[0]
    labels = list(map(int, re.findall(r'\d+', label_text)))
    assert len(labels) == len(set(labels)) == 216 and labels[-1] == 230
    rename = {301: 102, 302: 120, 254: 230}
    relabeled = {(rename.get(s, s), b): (w, d, rename.get(n, n))
                 for (s, b), (w, d, n) in native.items()}
    assert {(labels[s], b): (w, d, labels[n]) for (s, b), (w, d, n) in dense.items()} == relabeled
    text = (q / 'Prog215.v').read_text()
    body = text.split('Definition p215_tab', 1)[1].split('].', 1)[0]
    nodes = [((a, int(x or 0)), (b, int(y or 0))) for a, x, b, y in
             re.findall(r'\((C[IDBNCH])\s*(\d*)\s*,\s*(C[IDBNCH])\s*(\d*)\)', body)]
    assert len(nodes) == 179 and 'root := 178; nnodes := 179' in text
    for i, pair in enumerate(nodes):
        assert all(op != 'CN' or k < i for op, k in pair)

    def expand(edge, path=''):
        op, k = edge
        if op != 'CN':
            return [[path, op, None if op == 'CH' else k]]
        return expand(nodes[k][0], path + '0') + expand(nodes[k][1], path + '1')

    sites = expand(('CN', 178))
    assert sites == doc(candidate / 'sites215.json') and len(sites) == 4751
    assert len({(op, k) for _, op, k in sites}) == 23
    failed = []
    for p in sorted((build / 'attempts').glob('*/run*/record.json')):
        rec = doc(p)
        if rec['status'] != 'PASS':
            failed.append({'path': str(p), 'status': rec['status'], 'exit_code': rec.get('exit_code')})
    assert len(failed) == 1 and 'DomRho8/run1' in failed[0]['path'] and failed[0]['exit_code'] == -15
    owner = doc(build / 'actual-review.json')
    assert owner['status'] == 'PASS_CLOSED_KERNEL'
    assert owner['plan_sha256'] == bind(build / 'plan.json')
    assert owner['module_record_sha256'] == {n: selected[n]['record_sha256'] for n in order}
    assert owner['kernel_record_sha256'] == bind(kp)
    assert before == {p: digest(p) for p in before}, 'Input drift during independent audit'
    result = {'status': 'INDEPENDENT_ROCQ_ACTUAL_PEER_PASS', 'scope':
              'Read-only source, snapshot, dependency, object, raw log, exact argv and literal artifact audit. '
              'No compiler, kernel checker, supplied reviewer, or machine simulation invoked.',
              'module_count': 237, 'reference_count': 195, 'K215_count': 42,
              'exact_target_closure_and_topological_order': True,
              'endpoint_assumptions': endpoints, 'endpoint_axioms': [],
              'kernel_imported_utility_axioms': utility_axioms,
              'kernel_context_is_not_endpoint_assumption_set': True,
              'kernel_record_sha256': bind(kp), 'kernel_seconds': kernel['seconds'],
              'source_compile_seconds': seconds, 'toolchain': tc,
              'toolchain_scope': 'Actual records bind compiler/checker hashes and reported versions; current '
                                 'binaries match. Installed stdlib is the declared external boundary; no '
                                 'historical per-object stdlib before-map is invented.',
              'accepted_artifact_pins': pins, 'working_states': 215, 'actions': 430,
              'source_internal_nodes': 179, 'primitive_kinds': 23, 'shared_subtrees': 202,
              'expanded_source_leaves': 4751, 'preserved_failed_attempts': failed,
              'fully_instantiated_endpoint': 'Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥; '
                                             'and its negation equivalence, without hypotheses.',
              'no_internal_PA_or_encoded_ZFC_derivation_claim': True,
              'Lean_completion_claim': False, 'all_inputs_unchanged': True,
              'input_sha256': before, 'module_bindings': selected}
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as f:
        f.write(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'module_count', 'endpoint_axioms',
                                           'working_states', 'actions', 'expanded_source_leaves']}, indent=2))


if __name__ == '__main__':
    main()
