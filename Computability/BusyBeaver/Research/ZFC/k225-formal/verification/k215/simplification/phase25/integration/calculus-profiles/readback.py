"""Owned read-only acceptance of one specified direct-profile axiom reduction."""
from pathlib import Path
import argparse, hashlib, json, re
ROOT = Path('/tmp/k215-phase25-calculus-profiles-v1')
INTEGRATION = Path('/tmp/k215-phase25-integration')
RECEIPT_SHA = '3631c3de76500bfd91738eed4bf856fa134feba8d4f1520d6d48771f0d660cf7'
DRIVER = Path('/tmp/k215-phase25-calculus-profiles-draft-v2/compare_profiles.py')
PROBE = DRIVER.with_name('CalculusProfiles.lean')
NAMES = ['SetTheory.' + n for n in ['cons_sub', 'mem_map_sub', 'map_rename_up_S', 'Prov_rename', 'generalize_fresh', 'Prov_cut', 'soundness']]
OLD = [[n, ['propext'] if i == 0 else ['propext', 'Classical.choice', 'Quot.sound'] if i == 6 else ['propext', 'Quot.sound']] for i, n in enumerate(NAMES)]
NEW = [[NAMES[0], []]] + OLD[1:]
REPORT = re.compile(r"'([^'\r\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())
def profiles(text):
    result, position = [], 0
    for match in REPORT.finditer(text):
        assert not text[position:match.start()].strip(), 'Unparsed compiler output'
        atoms = [] if match[2] is None or not match[2].strip() else [a.strip() for a in match[2].split(',')]
        assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', a) for a in atoms)
        assert len(atoms) == len(set(atoms))
        result.append([match[1], atoms]); position = match.end()
    assert not text[position:].strip() and [n for n, _ in result] == NAMES
    return result
def main():
    parser = argparse.ArgumentParser(); parser.add_argument('--out', type=Path, required=True); args = parser.parse_args()
    assert not args.out.exists() and not args.out.is_symlink()
    receipt = Path(__file__).with_name('input-receipt.json'); assert sha(receipt) == RECEIPT_SHA
    pins = read(receipt)['files']; assert len(pins) == 45
    for path, digest in pins.items(): assert sha(path) == digest, path
    before = read(ROOT / 'before.json'); comparison = read(ROOT / 'comparison.json')
    assert len(before['inputs']) == 28 and all(pins[p] == h for p, h in before['inputs'].items())
    assert comparison['status'] == 'FAIL_PROFILE_DISCREPANCY' and comparison['all_inputs_postchecked'] is True
    assert comparison['metadata'] == before['metadata'] and set(comparison['runs']) == set(before['closures']) == {'old', 'new'}
    assert sha(PROBE) == before['probe_sha256'] == comparison['same_probe_sha256']
    assert PROBE.read_text() == 'import FirstOrder.Calculus\n\n' + ''.join('#print axioms ' + n + '\n' for n in NAMES)
    job = read(INTEGRATION / 'calculus-profiles-job.json'); outer = read(INTEGRATION / 'calculus-profiles-job-outer.json')
    assert all(sha(p) == h == pins[p] for p, h in job['pins'].items())
    assert outer['status'] == 'FAIL' and outer['exit_code'] == 1 and outer['argv'] == job['argv']
    assert outer['job_sha256'] == sha(INTEGRATION / 'calculus-profiles-job.json')
    for suffix in ['stdout', 'stderr']: assert outer[suffix + '_sha256'] == sha(INTEGRATION / ('calculus-profiles-job.' + suffix))
    assert (INTEGRATION / 'calculus-profiles-job.stdout').read_text() == 'PROBE old\nPROBE new\n'
    assert (INTEGRATION / 'calculus-profiles-job.stderr').read_text().endswith('AssertionError: Exact old/new ordered axiom profiles differ; original logs retained.\n')
    actual = {}; toolchains = []
    for side, expected in [('old', OLD), ('new', NEW)]:
        meta = before['metadata'][side]; basis = Path(meta['directory']); selected = before['closures'][side]
        result = read(basis / 'result.json'); plan_path = basis.parent / 'candidate-plan.json'; plan = read(plan_path)
        assert result['status'] == 'PASS' and sha(basis / 'result.json') == meta['result_sha256']
        assert sha(plan_path) == meta['plan_sha256'] == result['map_sha256']
        for name in ['inventory', 'completed']: assert sha(basis / (name + '.json')) == result[name + '_sha256']
        inventory = read(basis / 'inventory.json')['modules']; done = read(basis / 'completed.json')
        rows = {r['module']: r for r in inventory}; assert inventory == plan['modules']
        assert len(rows) == len(inventory) == len(done) == result['provider_count'] and set(rows) == set(done)
        assert len(rows) == (230 if side == 'old' else 35)
        tc = read(basis / 'toolchain.json'); toolchains.append(tc)
        for key in ['lean', 'lake', 'Init.olean', 'project_toolchain']: assert sha(tc[key]['path']) == tc[key]['sha256']
        assert set(selected) == {'FirstOrder.Calculus', 'FirstOrder.Fol'}
        for module, entry in selected.items():
            rec = done[module]; deps = [] if module == 'FirstOrder.Fol' else ['FirstOrder.Fol']
            assert rows[module]['imports'] == deps and rec['status'] == 'PASS'
            assert rec.get('exit_code', 0) == 0 and not rec.get('timed_out', False)
            assert sha(entry['source']) == entry['source_sha256'] == rec['source_sha256'] == rows[module]['source_sha256']
            assert sha(entry['object']) == entry['object_sha256'] == rec['object_sha256']
            assert entry['dependencies'] == rec['dependencies'] == {d: done[d]['object_sha256'] for d in deps}
            assert sha(rec['log']) == rec['log_sha256']
            assert not any(s in Path(rec['log']).read_text() for s in ['warning:', 'error:', 'sorryAx'])
        folder = ROOT / side; run = comparison['runs'][side]; record = read(folder / 'record.json'); log = (folder / 'compiler.log').read_text()
        for name, key in [('record.json', 'record_sha256'), ('compiler.log', 'log_sha256'), ('CalculusProfiles.olean', 'object_sha256')]: assert sha(folder / name) == run[key]
        assert record['status'] == 'PASS' and record['exit_code'] == 0 and record['timed_out'] is False
        assert record['timeout_seconds'] == 120 and record['memory_mebibytes'] == 12288
        assert record['module'] == 'CalculusProfiles' and record['source'] == str(PROBE) and record['source_sha256'] == sha(PROBE)
        assert record['command'] == [tc['lean']['path'], '-j1', '-M12288', '--root=' + str(PROBE.parent), '-o', str(folder / 'CalculusProfiles.olean'), str(PROBE)]
        assert record['lean_path'] == str(basis / 'objects') and record['compiler_sha256'] == tc['lean']['sha256']
        assert record['helper_sha256'] == pins[str(Path(job['cwd']) / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py')]
        assert record['dependencies'] == {m: e['object_sha256'] for m, e in selected.items()} and record['basis'] == meta
        assert record['seconds'] == run['seconds'] and record['log_sha256'] == run['log_sha256']
        actual[side] = profiles(log); assert actual[side] == run['profiles'] == expected
    assert toolchains[0] == toolchains[1] and actual['old'][1:] == actual['new'][1:] and actual['old'] != actual['new']
    for path, digest in pins.items(): assert sha(path) == digest, path
    assert sha(receipt) == RECEIPT_SHA
    output = {'status': 'PASS_SPECIFIED_AXIOM_REDUCTION_SIX_UNCHANGED_PROFILES', 'original_comparison_status': comparison['status'], 'original_outer_status': outer['status'], 'original_comparison_sha256': sha(ROOT / 'comparison.json'), 'reader_sha256': sha(__file__), 'input_receipt_sha256': RECEIPT_SHA, 'files_postchecked': len(pins), 'before_inputs_postchecked': len(before['inputs']), 'profiles': actual, 'both_supervisor_records_pass_zero_warnings_sorry': True, 'all_inputs_postchecked': True, 'scope': 'Readback only: seven direct declarations; specified cons_sub [propext] to [] and six exact ordered profiles. Original strict FAIL preserved. No compiler execution, full endpoint acceptance, performance claim or change to full 93/5/10 profile gates.'}
    with args.out.open('x') as stream: json.dump(output, stream, indent=2); stream.write('\n')
    print(output['status'], sha(args.out))
if __name__ == '__main__': main()
