#!/usr/bin/env python3
"""Fresh staged inference and kernel validation; Python standard library only.

Executable inference is untrusted certificate production. The generated data
is subsequently checked against both literal source trees by decide +kernel.
No preexisting project objects are imported and no generator correctness is assumed.
Requires Lean 4.32.0; the standard Lean installation is inherited.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', required=True)
    ap.add_argument('--out', required=True, type=Path,
                    help='Fresh output directory; must not exist')
    ap.add_argument('--memory-mb', type=int, default=4000)
    ap.add_argument('--resume', action='store_true',
                    help='Resume only hash-bound successful objects from this fresh build')
    a = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=a.resume)
    srcroot = out/'sources'
    objroot, logroot = out/'objects', out/'logs'
    if not a.resume:
        srcroot.mkdir()
        shutil.copytree(root/'BusyBeaver', srcroot/'BusyBeaver')
        shutil.copyfile(root/'KSource215AutoEmit.lean', srcroot/'KSource215AutoEmit.lean')
        objroot.mkdir(); logroot.mkdir()
    lean = Path(a.lean).resolve()
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    env = dict(os.environ, LEAN_PATH=str(objroot))
    target = 'BusyBeaver.ZFC.KSource215Auto'
    receipt = dict(version=version, target=target, records=[], complete=False,
                   mode='fresh staged generator and kernel validation',
                   preexisting_project_objects_imported=0, memory_mb=a.memory_mb,
                   full_binary_or_zfc_endpoint=False)
    if a.resume:
        receipt = json.loads((out/'receipt.json').read_text())
        assert receipt['version'] == version
        assert receipt['complete'] is False
        failures = [dict(x) for x in receipt['records']
                    if x['exit_code'] or x['placeholder_detected']]
        for index, failed in enumerate(failures):
            original_log = out/failed['log']
            saved_log = logroot/(failed['module']+f'.failed-{index}.log')
            shutil.copyfile(original_log, saved_log)
            assert sha(saved_log) == failed['log_sha256']
            failed['log'] = str(saved_log.relative_to(out))
        receipt.setdefault('failed_attempts', []).extend(failures)
        receipt['records'] = [x for x in receipt['records']
                              if not x['exit_code'] and not x['placeholder_detected']]
        receipt['resumed_after_resource_limit'] = True
        receipt['memory_mb'] = a.memory_mb
        receipt['preexisting_project_objects_imported'] = 0
        receipt.pop('project_objects_reused', None)

    def save():
        (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')

    def run(label, command, source, object_path=None):
        log = logroot/(label+'.log')
        start = time.monotonic()
        with log.open('w') as f:
            p = subprocess.Popen(command, cwd=srcroot, env=env,
                                 stdout=f, stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(p.pid, 0)
            rc = os.waitstatus_to_exitcode(status)
            p.returncode = rc
        contents = log.read_text()
        bad = 'sorryAx' in contents or "uses 'sorry'" in contents
        row = dict(module=label, command=command, exit_code=rc,
                   seconds=round(time.monotonic()-start, 3),
                   max_rss_kib=usage.ru_maxrss, source_sha256=sha(source),
                   log=str(log.relative_to(out)), log_sha256=sha(log),
                   placeholder_detected=bad)
        if object_path is not None:
            row['object_sha256'] = sha(object_path) if rc == 0 else None
        receipt['records'].append(row); save()
        print(json.dumps(row), flush=True)
        if rc or bad:
            print(contents)
            raise SystemExit(1)

    seen = set()
    def compile_module(name):
        if name in seen:
            return
        source = srcroot/(name.replace('.', '/')+'.lean')
        for line in source.read_text().splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('BusyBeaver.'):
                        compile_module(dep)
                    elif dep != 'Init':
                        raise ValueError('Unexpected project import: '+dep)
        obj = objroot/(name.replace('.', '/')+'.olean')
        if a.resume:
            previous = [x for x in receipt['records'] if x['module'] == name]
            if previous:
                bound = previous[-1]
                delivered = root/(name.replace('.', '/')+'.lean')
                assert sha(source) == sha(delivered) == bound['source_sha256'], name
                assert sha(obj) == bound['object_sha256'], name
                assert sha(out/bound['log']) == bound['log_sha256'], name
                seen.add(name)
                return
        obj.parent.mkdir(parents=True, exist_ok=True)
        run(name, [str(lean), '-j1', f'-M{a.memory_mb}', '-o', str(obj), str(source)], source, obj)
        seen.add(name)

    # Fresh dependencies for executable inference; it supplies no premise.
    compile_module('BusyBeaver.ZFC.RMAutoCertificate')
    compile_module('BusyBeaver.ZFC.KSource215Data')
    emitter = srcroot/'KSource215AutoEmit.lean'
    generated = out/'generated'
    if a.resume:
        assert sha(emitter) == sha(root/'KSource215AutoEmit.lean')
    run('KSource215AutoEmit' + ('_resume' if a.resume else ''),
        [str(lean), '-j1', f'-M{a.memory_mb}', '--run',
         str(emitter), str(generated)], emitter)
    cached = root/'BusyBeaver/ZFC/KSource215AutoData.lean'
    emitted = generated/'KSource215AutoData.lean'
    receipt['emission'] = json.loads((generated/'emission.json').read_text())
    receipt['emission'].update(generated_source_sha256=sha(emitted),
                               delivered_cache_sha256=sha(cached),
                               matches_delivered_cache=sha(emitted)==sha(cached),
                               entries_sha256=sha(generated/'entries.json'))
    shutil.copyfile(emitted, srcroot/'BusyBeaver/ZFC/KSource215AutoData.lean')
    save()
    # Every source-equivalence obligation is validated in the kernel.
    compile_module(target)
    receipt.update(complete=True, compiled_project_modules=len(seen),
                   compiler_seconds=sum(x['seconds'] for x in receipt['records']
                                        if 'object_sha256' in x),
                   total_seconds=sum(x['seconds'] for x in receipt['records']),
                   failed_attempt_seconds=sum(x['seconds'] for x in receipt.get('failed_attempts', [])),
                   peak_rss_kib=max(x['max_rss_kib'] for x in receipt['records']))
    save()
    print(json.dumps({k:receipt[k] for k in ['complete','compiled_project_modules',
                        'compiler_seconds','total_seconds','peak_rss_kib']}), flush=True)


if __name__ == '__main__':
    main()
