"""Stage exact evidence after three successful commands; never run a checker or edit the repository."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse, fcntl, functools, hashlib, json, re, runpy
NATIVE = Path('/tmp/gowers-next297-native-tools')
PINS = {'common.py': '4c71aedd3ec630046fd5dd5d205e250893c93bb0b1f1d2b0faf69bfe89e07328',
        'capture.py': '8463cc8e288255e12fd9ad777f8a2fe7f0a75aa6cbf888f423129a112f6cecd2',
        'run.py': 'bf1aa169ed14fc098fd20c57a93a8c9904718bfc2b2648997384a3effd61e83a'}
for name, expected in PINS.items():
    if hashlib.sha256((NATIVE / name).read_bytes()).hexdigest() != expected:
        raise RuntimeError('Frozen native tool changed: ' + name)
sys.path.insert(0, str(NATIVE))
from common import *
verify_prior = runpy.run_path(str(NATIVE / 'run.py'), run_name='archive_verifier')['verify_prior']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', nargs=2, metavar=('PATH', 'SHA256'), required=True)
    parser.add_argument('--source-ledger', nargs=2, metavar=('PATH', 'SHA256'), required=True)
    for mode in ('core', 'shared', 'supplemental'):
        parser.add_argument('--' + mode, nargs=2, metavar=('RECEIPT', 'SHA256'), required=True)
    parser.add_argument('--extra-evidence', nargs=2, metavar=('MANIFEST', 'SHA256'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); evidence = {}; by_source = {}
    def bind(path, expected, destination):
        path = Path(path).resolve()
        require(bool(re.fullmatch('[0-9a-f]{64}', expected)) and sha(path) == expected, 'Evidence hash mismatch: ' + str(path))
        require(not Path(destination).is_absolute() and '..' not in Path(destination).parts, 'Unsafe archive destination')
        if str(path) in by_source:
            previous = by_source[str(path)]
            require(evidence[previous]['sha256'] == expected, 'Conflicting pin'); return previous
        require(destination not in evidence, 'Archive destination collision')
        evidence[destination] = {'original_path': str(path), 'sha256': expected}
        by_source[str(path)] = destination; return destination
    snapshot_path = Path(args.snapshot[0]).resolve(); snapshot_hash = args.snapshot[1]
    bind(snapshot_path, snapshot_hash, 'snapshot.json'); snapshot = json.loads(snapshot_path.read_text())
    require(snapshot['source_commit'] == '6a753d0702d1691c25a21bdbdb58e29412931be5', 'Wrong batch source')
    require(same(snapshot['tools'], {str(NATIVE / name): value for name, value in PINS.items()}), 'Native tool keyset/pins mismatch')
    root = Path(snapshot['root']); worker_check(root)
    lock_path = Path('/tmp') / ('gowers-native-' + hashlib.sha256(str(root).encode()).hexdigest()[:16] + '.lock')
    lock = lock_path.open('a'); fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    guard = source_guard(snapshot)
    for path, expected in snapshot['tools'].items(): bind(path, expected, 'tools/' + Path(path).name)
    bind(snapshot['plan']['path'], snapshot['plan']['sha256'], 'tools/plan.json')
    bind(__file__, sha(__file__), 'tools/archive.py')
    ledger_destination = bind(*args.source_ledger, 'source-ledger.json')
    ledger = json.loads(Path(args.source_ledger[0]).read_text())
    require(ledger['source_commit'] == snapshot['source_commit'], 'Source ledger commit mismatch')
    if args.extra_evidence:
        bind(*args.extra_evidence, 'extra-evidence-manifest.json')
        extra = json.loads(Path(args.extra_evidence[0]).read_text())
        for label, item in extra.items():
            require(bool(re.fullmatch('[A-Za-z0-9_.-]+', label)) and set(item) == {'path', 'sha256'}, 'Invalid extra evidence item')
            bind(item['path'], item['sha256'], 'extra/' + label + '/' + Path(item['path']).name)
    receipts = {}; commands = []; previous_ref = None; previous_recorded = None
    for mode in ('core', 'shared', 'supplemental'):
        path, expected = getattr(args, mode); path = Path(path).resolve()
        receipt, actual_files = verify_prior(path, expected, snapshot, snapshot_hash, mode, guard)
        require(receipt['snapshot_path'] == str(snapshot_path), 'Receipt snapshot path mismatch')
        require(same(receipt['previous_receipt'], previous_ref), 'Broken sequential receipt chain')
        require(Path(receipt['log']).resolve() == path.parent / 'native.log', 'Unexpected native log location')
        if previous_recorded is not None:
            require(datetime.datetime.fromisoformat(previous_recorded) <= datetime.datetime.fromisoformat(receipt['started_at']), 'Commands are not sequential')
        for filename, actual_hash in actual_files.items(): bind(filename, actual_hash, 'attempts/' + mode + '/' + Path(filename).name)
        previous_ref = {'path': str(path), 'sha256': expected}; previous_recorded = receipt['recorded_at']
        receipts[mode] = receipt
        commands.append({'mode': mode, 'receipt': by_source[str(path)], 'receipt_sha256': expected,
                         'command': receipt['command'], 'terminal_exit': receipt['terminal_exit'],
                         'terminal_module_count': receipt['terminal_module_count'],
                         'started_at': receipt['started_at'], 'finished_at': receipt['finished_at']})
    @functools.lru_cache(None)
    def closure(module):
        return frozenset({module}).union(*(closure(d) for d in snapshot['graph'][module] if local(d)))
    own_roots = []
    for mode, spec in snapshot['modes'].items():
        for target in spec['roots']:
            modules = sorted(closure(target))
            own_roots.append({'invocation': mode, 'target': target, 'modules': len(modules),
                              'inputs_with_three_configurations': len(modules) + len(CONFIGS),
                              'source_lines': sum(len((root / module_path(m)).read_text().splitlines()) for m in modules),
                              'ordered_closure_sha256': hashlib.sha256(canonical(modules).encode()).hexdigest()})
    current_artifacts = artifacts(snapshot, snapshot['modes']['supplemental']['cumulative_modules'], True)
    require(same(current_artifacts, receipts['supplemental']['artifacts_after']), 'Current combined artifacts changed')
    output = args.output
    require(output.is_absolute() and output.resolve().is_relative_to(Path('/tmp')) and output.parent.is_dir() and not output.exists(), 'Use a new /tmp archive directory')
    protected = {str(root / p): stamp(root / p) for p in snapshot['source_hashes']}
    protected.update({item['original_path']: stamp(item['original_path']) for item in evidence.values()})
    output.mkdir()
    for destination, item in evidence.items():
        data = Path(item['original_path']).read_bytes()
        require(hashlib.sha256(data).hexdigest() == item['sha256'], 'Evidence changed during copy')
        target = output / destination; target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream: stream.write(data)
        target.chmod(0o444); require(sha(target) == item['sha256'], 'Archive copy differs')
    require(same(source_guard(snapshot), guard), 'Source guard changed during archive')
    require(same(artifacts(snapshot, snapshot['modes']['supplemental']['cumulative_modules'], True), current_artifacts), 'Artifacts changed during archive')
    for path, expected_stamp in protected.items(): require(stamp(path) == expected_stamp, 'Protected input changed during archive')
    for destination, item in evidence.items():
        require(sha(item['original_path']) == item['sha256'] and sha(output / destination) == item['sha256'], 'Final evidence hash mismatch')
    worker_check(root)
    write_new(output / 'evidence-map.json', {'schema_version': 1, 'source_commit': snapshot['source_commit'], 'files': evidence})
    index = {'schema_version': 1, 'status': 'passed: exact actual evidence staged; repository unchanged',
             'source_commit': snapshot['source_commit'], 'snapshot': {'path': 'snapshot.json', 'sha256': snapshot_hash},
             'source_ledger': {'path': ledger_destination, 'sha256': args.source_ledger[1]},
             'evidence_map': {'path': 'evidence-map.json', 'sha256': sha(output / 'evidence-map.json')},
             'actual_invocations': commands, 'combined_native_artifact_count': len(current_artifacts),
             'artifact_evidence': 'attempts/supplemental/receipt.json',
             'per_root_closures_are_metadata_only': True,
             'closure_reconstruction': 'Follow local imports in snapshot.graph; sort module names; hash compact sorted-key JSON UTF-8 without newline.',
             'root_closure_metadata': own_roots,
             'limitations': ['No per-root native command outcomes are asserted.',
                            'Artifact freshness/stability uses checker input mtimes and artifact mtime_ns/size, not content hashes.',
                            'Source inventory and aggregate facades are protected inputs; this does not certify paper fidelity or every export.'],
             'verified_at': now()}
    write_new(output / 'index.json', index)
    print(json.dumps({'status': 'passed', 'archive': str(output), 'copied_evidence_files': len(evidence),
                      'index_sha256': sha(output / 'index.json'), 'evidence_map_sha256': sha(output / 'evidence-map.json'),
                      'combined_modules': len(current_artifacts)}, indent=2))
if __name__ == '__main__': main()
