"""Read and verify the frozen sharing packet; never run its producer or Lean."""
import argparse, ast, hashlib, io, json, re, tarfile
from pathlib import Path, PurePosixPath

def sha(data):
    return hashlib.sha256(data).hexdigest()

def load(packet):
    summary = json.loads((packet / 'summary.json').read_bytes())
    raw = (packet / 'evidence.tar.gz').read_bytes()
    index_raw = (packet / 'index.json').read_bytes()
    assert sha(raw) == summary['archive_sha256']
    assert sha(index_raw) == summary['index_sha256']
    index = json.loads(index_raw)
    files = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as tar:
        for member in tar:
            p = PurePosixPath(member.name)
            assert member.isfile() and not p.is_absolute() and '..' not in p.parts
            assert member.name not in files
            assert not member.name.endswith(('.olean', '.olean.server', '.olean.private', '.ilean', '.pyc', '.vo', '.vos', '.vok'))
            assert member.name in index
            data = tar.extractfile(member).read()
            assert len(data) == index[member.name]['bytes']
            assert sha(data) == index[member.name]['sha256']
            files[member.name] = data
    assert set(files) == set(index)
    paths = json.loads(files['paths.json'])
    assert set(paths.values()) <= set(files)
    return summary, files, paths

def review(packet):
    summary, files, paths = load(packet)
    source = files['candidate/DomRho8.lean']
    producer = files['candidate/generate_domrho8_lean.py']
    previous = files['history/generate_domrho8_lean-v1.py']
    assert sha(source) == summary['source_sha256']
    assert sha(producer) == summary['producer_sha256']
    assert sha(previous) == summary['historical_producer_sha256']
    assert ast.dump(ast.parse(previous)) == ast.dump(ast.parse(producer))
    assert b''.join(x.rstrip(b' \t\r\n') + b'\n' for x in previous.splitlines(True)) == producer
    kernel = json.loads(files['kernel/result.json'])
    assert sha(files['kernel/result.json']) == summary['kernel_result_sha256']
    assert kernel['status'] == 'PASS' and kernel['exit_code'] == 0 and not kernel['timed_out']
    assert kernel['warnings'] == 0 and kernel['axiom_reports'] == ['propext, Quot.sound'] * 4
    assert kernel['inputs_unchanged'] and kernel['providers_unchanged'] and kernel['basis_unchanged']
    assert len(kernel['providers']) == 10
    assert sha(files['kernel/SharedWithAudit.lean']) == kernel['source_sha256']
    assert source + files['candidate/APIAudit.lean.inc'] == files['kernel/SharedWithAudit.lean']
    log = files['kernel/compiler.log']
    assert sha(log) == kernel['log_sha256']
    assert re.findall(rb'depends on axioms: \[([^\]]*)\]', log) == [b'propext, Quot.sound'] * 4
    assert not re.search(rb'(?i)(warning:|error:|sorryAx)', log)
    for key, name in [('result', 'result'), ('inventory', 'inventory'), ('completed', 'completed')]:
        assert sha(files[f'basis/phase3-{name}.json']) == kernel[f'basis_{key}_sha256']
    assert sha(files['tools/executed-run-locked-helper.py']) == kernel['helper_sha256']
    assert sha(files['tools/executed-kernel-supervisor.py']) == kernel['supervisor_sha256']
    for run, record_key in [('reproduction1', 'renderer_v1_result_sha256'), ('reproduction2', 'renderer_v2_result_sha256')]:
        record_raw = files[f'generation/{run}/result.json']
        assert sha(record_raw) == summary[record_key]
        r = json.loads(record_raw)
        assert r['status'] == 'PASS' and r['inputs_before'] == r['inputs_after'] and r['inputs_unchanged']
        assert len(r['inputs_before']) == 6
        for path, digest in r['inputs_before'].items():
            assert sha(files[paths[path]]) == digest
        assert len(r['cases']) == 7
        for row in r['cases']:
            if 'output_sha256' in row:
                assert row['exit_code'] == 0
                assert sha(files[paths[row['command'][4]]]) == row['output_sha256'] == row['expected']
            else:
                assert row['exit_code'] != 0 and row['output_absent']
                assert row['command'][4] not in paths
        assert r['generated_plus_five_api_clients_equals_kernel_snapshot']
        assert r['typed_snapshot_sha256'] == kernel['source_sha256']
    compare = json.loads(files['comparison/source-comparison.json'])
    assert compare['all117_retained_statements_exact']
    assert compare['public_header_and_complete_deduction_tail_byte_identical']
    assert compare['generic_direct_emitter_suffix_byte_identical']
    assert len(source) == summary['new_source_bytes'] == 30114
    return {
        'status': 'PASS_SAVED_SHARING_EVIDENCE',
        'archive_sha256': summary['archive_sha256'],
        'source_sha256': sha(source), 'producer_sha256': sha(producer),
        'archive_members': len(files), 'no_compiled_objects': True,
        'kernel_sources_and_logs_bound': True, 'provider_bindings_recorded': 10,
        'renderer_versions_checked': 2, 'successful_modes_each': 5, 'rejected_modes_each': 2,
        'scope': 'Rehashed saved text evidence, not a new generator/kernel run or a rehash of absent provider binaries.'
    }

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    result = review(args.packet)
    text = json.dumps(result, indent=2) + '\n'
    if args.out:
        assert not args.out.exists()
        args.out.write_text(text)
    print(text, end='')
