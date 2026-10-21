#!/usr/bin/env python3
"""Incrementally rebuild DomRho8's reverse closure from an audited baseline.

No prior object is overwritten. Unchanged objects are copied and pinned to their
successful baseline records; all changed-source dependents compile afresh. The
focused recursive coqchk target is DomRho8, not the complete set-theory endpoint.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import importlib.util
import json
import os
import shutil
import signal
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--driver', type=Path, required=True)
    args = parser.parse_args()
    base, out = args.baseline.resolve(), args.output.resolve()
    assert not out.exists(), 'Use a fresh output directory'
    out.mkdir()
    spec = importlib.util.spec_from_file_location('reviewed_driver', args.driver)
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    signal.signal(signal.SIGTERM, driver.stop_signal)
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('900 second proof cap')))
    oldplan = json.loads((base / 'plan.json').read_text())
    oldaudit = json.loads((base / 'actual-review.json').read_text())
    assert oldaudit['status'] == 'PASS_CLOSED_KERNEL'
    cmd = ['python3', '-B', str(args.driver), '--reference', str(base / 'k230-rocq'),
           '--jeff-reference', str(base / 'jeff-busy-beaver'), '--output', str(out), '--plan-only']
    subprocess.run(cmd, check=True, stdout=(out / 'plan-output.log').open('w'), stderr=subprocess.STDOUT)
    plan = json.loads((out / 'plan.json').read_text())
    assert plan['order'] == oldplan['order'] and len(plan['order']) == 237
    oldrecords = {}
    changed = set()
    originals = {}
    for name in plan['order']:
        record_path = base / 'records' / (name + '.json')
        record = json.loads(record_path.read_text())
        assert record['status'] == 'PASS' and record['exit_code'] == 0 and record['post_inputs_unchanged']
        snap = Path(record['source_snapshot'])
        assert sha(snap) == record['source_sha256']
        assert sha(snap.parent / 'output.log') == record['output_sha256']
        assert driver.endpoint_gate(name, (snap.parent / 'output.log').read_text())
        obj = Path(oldplan['modules'][name]['target']).with_suffix('.vo')
        assert sha(obj) == record['object_sha256']
        originals[str(obj)] = sha(obj)
        source = Path(plan['modules'][name]['source'])
        if sha(source) != record['source_sha256']:
            changed.add(name)
        for path, digest in record['inputs'].items():
            if path != str(source):
                assert sha(path) == digest
        oldrecords[name] = {'record': record, 'record_sha256': sha(record_path)}
    assert changed == {'K215F.DomRho8'}, changed
    affected = set(changed)
    for name in plan['order']:
        assert plan['modules'][name]['dependencies'] == oldplan['modules'][name]['dependencies']
        if set(plan['modules'][name]['dependencies']) & affected:
            affected.add(name)
    assert len(affected) == 7
    shutil.copytree(base / 'work', out / 'work', dirs_exist_ok=True)
    reuse = {}
    for name in plan['order']:
        target = Path(plan['modules'][name]['target'])
        assert sha(target.with_suffix('.vo')) == oldrecords[name]['record']['object_sha256']
        if name not in affected:
            assert sha(target) == sha(plan['modules'][name]['source'])
            reuse[name] = {'source_sha256': sha(target),
                          'object_sha256': sha(target.with_suffix('.vo')),
                          'baseline_record_sha256': oldrecords[name]['record_sha256']}
    write(out / 'reuse.json', reuse)
    env = json.loads(subprocess.check_output(['opam', 'exec', '--switch=proofs-rocq91', '--',
                      'python3', '-c', 'import os,json; print(json.dumps(dict(os.environ)))'], text=True))
    compiler = Path(shutil.which('coqc', path=env['PATH']))
    checker = compiler.with_name('coqchk')
    toolchain = json.loads((base / 'toolchain.json').read_text())
    assert sha(compiler) == toolchain['coqc_sha256']
    assert sha(checker) == toolchain['coqchk_sha256']
    write(out / 'toolchain.json', toolchain)
    write(out / 'basis.json', {'baseline_plan_sha256': sha(base / 'plan.json'),
          'baseline_actual_review_sha256': sha(base / 'actual-review.json'),
          'reviewed_driver_sha256': sha(args.driver), 'changed': sorted(changed),
          'affected': [n for n in plan['order'] if n in affected],
          'reused_modules': len(reuse), 'focused_kernel_target': 'K215F.DomRho8'})
    records = out / 'records'
    records.mkdir()
    for name in plan['order']:
        if name not in affected:
            continue
        item = plan['modules'][name]
        source, target = Path(item['source']), Path(item['target'])
        inputs = {str(source): sha(source)}
        for dep in item['dependencies']:
            obj = Path(plan['modules'][dep]['target']).with_suffix('.vo')
            inputs[str(obj)] = sha(obj)
        shutil.copyfile(source, target)
        attempt = out / 'attempts' / name
        attempt.mkdir(parents=True)
        shutil.copyfile(source, attempt / source.name)
        argv = [str(compiler), *plan['flags'], '-w', '-deprecated,-notation-overridden', str(target)]
        record = {'module': name, 'argv': argv, 'inputs': inputs,
                  'source_sha256': sha(source), 'source_snapshot': str(attempt / source.name)}
        print('WAIT', name, flush=True)
        with open('/tmp/proveit-k215-proof-build.lock', 'a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            start = time.monotonic()
            print('START', name, flush=True)
            try:
                signal.alarm(900)
                with (attempt / 'output.log').open('w') as log:
                    proc = driver.proof_process(argv, env, out / 'work', log)
                record.update(exit_code=proc.returncode, seconds=time.monotonic() - start)
            except BaseException as err:
                record.update(status='INTERRUPTED', seconds=time.monotonic()-start, error=repr(err))
                write(attempt / 'record.json', record)
                raise
            finally:
                signal.alarm(0)
        text = (attempt / 'output.log').read_text()
        record.update(output_sha256=sha(attempt / 'output.log'),
                      closed_reports=text.count('Closed under the global context'),
                      post_inputs_unchanged=all(sha(p) == h for p, h in inputs.items()),
                      assumption_gate_passed=driver.endpoint_gate(name, text))
        record['status'] = ('PASS' if record['exit_code'] == 0 and record['post_inputs_unchanged']
                            and record['assumption_gate_passed'] else 'FAIL')
        if record['exit_code'] == 0:
            record['object_sha256'] = sha(target.with_suffix('.vo'))
        write(attempt / 'record.json', record)
        write(records / (name + '.json'), record)
        print(record['status'], name, record['seconds'], flush=True)
        assert record['status'] == 'PASS', text
    # Recheck the changed computational proof recursively, without admit/norec.
    kernel = out / 'kernel'
    kernel.mkdir()
    inputs = {str(Path(plan['modules'][n]['target']).with_suffix('.vo')):
              sha(Path(plan['modules'][n]['target']).with_suffix('.vo')) for n in plan['order']}
    argv = [str(checker), *plan['flags'], '-silent', '-o', 'K215F.DomRho8']
    print('WAIT focused coqchk', flush=True)
    with open('/tmp/proveit-k215-proof-build.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        start = time.monotonic()
        try:
            signal.alarm(900)
            with (kernel / 'output.log').open('w') as log:
                proc = driver.proof_process(argv, env, out / 'work', log)
        finally:
            signal.alarm(0)
    record = {'argv': argv, 'inputs': inputs, 'exit_code': proc.returncode,
              'seconds': time.monotonic()-start, 'output_sha256': sha(kernel / 'output.log'),
              'post_inputs_unchanged': all(sha(p) == h for p, h in inputs.items())}
    write(kernel / 'record.json', record)
    assert proc.returncode == 0 and record['post_inputs_unchanged']
    assert all(sha(p) == h for p, h in originals.items())
    write(out / 'result.json', {'status': 'PASS_INCREMENTAL_ENDPOINTS_FOCUSED_KERNEL',
          'recompiled': [n for n in plan['order'] if n in affected], 'reused': len(reuse),
          'baseline_objects_unchanged': True, 'endpoint_closed_reports': 4,
          'kernel_target': 'K215F.DomRho8', 'kernel_record_sha256': sha(kernel / 'record.json'),
          'scope': 'Seven fresh dependent compilations and focused recursive changed-proof check; the immutable baseline supplies all230 reused objects and its earlier full237 recursive endpoint check.'})
    print('PASS_INCREMENTAL_ENDPOINTS_FOCUSED_KERNEL', flush=True)


if __name__ == '__main__':
    main()
