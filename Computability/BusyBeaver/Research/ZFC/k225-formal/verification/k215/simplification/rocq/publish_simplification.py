#!/usr/bin/env python3
"""Copy the completed incremental evidence without mutating its baseline."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import shutil
import tarfile


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--scratch', type=Path, required=True)
    ap.add_argument('--build', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    repo, scratch, build, out = (x.resolve() for x in (a.repo, a.scratch, a.build, a.output))
    result = json.loads((build / 'result.json').read_text())
    assert result['status'] == 'PASS_INCREMENTAL_ENDPOINTS_FOCUSED_KERNEL'
    assert not out.exists(), 'Publish to a fresh directory'
    out.mkdir(parents=True)
    actual = out / 'actual'
    actual.mkdir()
    for name in ('result.json', 'plan.json', 'basis.json', 'reuse.json', 'toolchain.json'):
        shutil.copyfile(build / name, actual / name)
    for name in ('attempts', 'records', 'kernel'):
        shutil.copytree(build / name, actual / name)
    for src, dst in [
        ('final-generation-v2.json', 'generation.json'),
        ('regeneration-review-v2.json', 'regeneration-review.json'),
        ('regenerated-v2/regeneration215.json', 'regeneration215.json'),
        ('regeneration-v2.log', 'regeneration.log'),
        ('incremental-v2.stdout', 'build.log')]:
        shutil.copyfile(scratch / src, actual / dst)
    for name in ('rebuild_dependents.py', 'publish_simplification.py'):
        shutil.copyfile(scratch / name, out / name)
    kf = repo / 'Computability/BusyBeaver/Research/ZFC/k225-formal'
    paths = [kf / 'rocq/rocq-extension/coq/215/DomRho8.v',
             kf / 'rocqdom/DomRho8Reflection.v', kf / 'generate_domrho8_rocq_compact.py',
             kf / 'rocq/rocq-extension/regenerate215.py',
             kf / 'lean217/dominated_rho8_full_certificate.json']
    ledger = {str(p.relative_to(repo)): {'sha256': sha(p), 'bytes': p.stat().st_size} for p in paths}
    for name in result['recompiled']:
        rec = json.loads((actual / 'records' / (name + '.json')).read_text())
        assert rec['status'] == 'PASS' and rec['post_inputs_unchanged'] and rec['assumption_gate_passed']
        src = Path(next(iter(rec['inputs'])))
        assert sha(src) == rec['source_sha256']
        snap = actual / 'attempts' / name / src.name
        log = snap.parent / 'output.log'
        assert sha(snap) == rec['source_sha256'] and sha(log) == rec['output_sha256']
        if name in ('K215F.Correct215', 'K215F.CorrectDense215'):
            assert log.read_text().count('Closed under the global context') == 2
            assert 'Axioms:' not in log.read_text()
    kernel = json.loads((actual / 'kernel/record.json').read_text())
    assert kernel['exit_code'] == 0 and kernel['post_inputs_unchanged']
    assert kernel['argv'][-1] == 'K215F.DomRho8'
    assert not {'-norec', '-admit'} & set(kernel['argv'])
    assert sha(actual / 'kernel/output.log') == kernel['output_sha256']
    write(out / 'source-bindings.json', {'status': 'PASS_CURRENT_SOURCE_BINDINGS', 'files': ledger})
    baseline = scratch / 'baseline-canonical/DomRho8.v'
    current = paths[0]
    final_record = json.loads((actual / 'records/K215F.DomRho8.json').read_text())
    comparison = {'old_source_sha256': sha(baseline), 'old_source_bytes': baseline.stat().st_size,
                  'new_source_sha256': sha(current), 'new_source_bytes': current.stat().st_size,
                  'old_lines': len(baseline.read_text().splitlines()),
                  'new_lines': len(current.read_text().splitlines()),
                  'byte_reduction_percent': 100 * (1 - current.stat().st_size / baseline.stat().st_size),
                  'original_certificate_nodes': 3728, 'retained_original_nodes': 674,
                  'interpreter_instructions': 780, 'term_data_entries': 297,
                  'original_compile_seconds': 8.174,
                  'new_compile_seconds': final_record['seconds'],
                  'timing_scope': 'Individual recorded invocations, excluding lock waits; not a controlled benchmark.'}
    write(out / 'comparison.json', comparison)
    # Retain illustrative actual experiments and the interrupted whitespace pass
    # compactly, without compiled objects or the copied baseline cache.
    history_files = []
    for number in ('run011', 'run012', 'run014', 'run015', 'run016'):
        for p in (scratch / 'attempts' / number).iterdir():
            if p.suffix in ('.v', '.json', '.log'):
                history_files.append((p, 'experiments/' + number + '/' + p.name))
    partial = build.with_name('k215-rocq-compact-incremental')
    for prefix in ('attempts', 'records'):
        for p in (partial / prefix).rglob('*'):
            if p.is_file():
                history_files.append((p, 'whitespace-predecessor/' + str(p.relative_to(partial))))
    history_files.append((partial / 'interruption.json', 'whitespace-predecessor/interruption.json'))
    history_files.append((scratch / 'incremental.stdout', 'whitespace-predecessor/build.log'))
    with open(out / 'history.tar.gz', 'wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode='w') as archive:
                for path, name in sorted(history_files, key=lambda pair: pair[1]):
                    info = archive.gettarinfo(str(path), arcname=name)
                    info.mtime = 0
                    info.uid = info.gid = 0
                    info.uname = info.gname = ''
                    with path.open('rb') as f:
                        archive.addfile(info, f)
    write(out / 'history-index.json', {name: {'sha256': sha(p), 'bytes': p.stat().st_size}
                                      for p, name in history_files})
    write(out / 'publication.json', {'status': 'PASS_ADDITIVE_INCREMENTAL_PUBLICATION',
          'source_ledger_sha256': sha(out / 'source-bindings.json'),
          'result_sha256': sha(actual / 'result.json'),
          'history_sha256': sha(out / 'history.tar.gz'),
          'scope': 'Seven rebuilt dependents,230 copied/hash-bound baselineobjects and a focused recursive DomRho8 check. The old full237 endpoint evidence is retained separately and was not replayed here.'})
    print(out)


if __name__ == '__main__':
    main()
