"""Replay the 13 selected batch-185 checks on fresh copies, without manifest/ancestor suites."""
from pathlib import Path
import argparse
import json
import os
import runpy
import shutil
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packets', type=Path, required=True, help='Directory from recover-intake185.py')
    parser.add_argument('--output', type=Path, required=True, help='New scratch output directory')
    args = parser.parse_args()
    packets, out = args.packets.resolve(), args.output.resolve()
    repo = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    if out == repo or repo in out.parents:
        parser.error('Use an output directory outside the repository')
    out.mkdir(parents=True, exist_ok=False)
    baseline = out / 'work/construction'
    alternative = out / 'work/alternatives'
    shutil.copytree(packets / 'K220_Construction_2026-10-20', baseline)
    shutil.copytree(packets / 'K220_Alternatives_2026-10-20', alternative)
    extract = runpy.run_path(str(Path(__file__).with_name('recover-intake185.py')))['extract']
    extract((baseline / 'portable/vendor/K221_Construction_2026-10-20.zip').read_bytes(), out / 'work/parent')
    parent = out / 'work/parent/K221_Construction_2026-10-20'
    jobs = []

    def run(name, script, argv, cwd, timeout=120):
        command = [sys.executable, '-B', str(script), *map(str, argv)]
        start = time.monotonic()
        log = out / (name + '.log')
        print(name, flush=True)
        with log.open('w') as stream:
            try:
                result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
                                        timeout=timeout, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
                code, timed_out = result.returncode, False
            except subprocess.TimeoutExpired:
                code, timed_out = None, True
        jobs.append(dict(name=name, command=command, cwd=str(cwd), exit_code=code,
                         timed_out=timed_out, seconds=time.monotonic()-start, log=str(log)))
        (out / 'actual.json').write_text(json.dumps(dict(jobs=jobs,
            scope='Selected fresh checks only; no manifest audit, recursive ancestor replay, or proof-assistant run.'), indent=2)+'\n')
        if code != 0 or timed_out:
            raise RuntimeError('Check failed; see ' + str(log))

    run('build220', baseline/'portable/build220.py', ['--baseline',parent,'--output',out/'build'], baseline)
    run('canonical-startup', baseline/'portable/canonicalize220.py',
        ['--table',out/'build/candidate.tm','--source',out/'build/sites.json','--output',out/'canonical'], baseline)
    run('full-runtime', baseline/'portable/check_runtime220.py',
        ['--baseline',parent,'--table',out/'build/candidate.tm','--sites',out/'build/sites.json','--output',out/'runtime'], baseline, 1200)
    run('independent-runtime-audit', baseline/'portable/audit_runtime220.py',
        ['--baseline',parent,'--table',out/'build/candidate.tm','--sites',out/'build/sites.json',
         '--runtime',out/'runtime','--driver',baseline/'portable/check_runtime220.py',
         '--prefold',out/'build/prefold.tm','--output',out/'independent-audit.json'], baseline)
    old = baseline/'machine/k220.native.tm'
    run('construct', alternative/'portable/construct.py', ['--baseline',old,'--output',out/'variants'], alternative)
    run('macro-diamonds', alternative/'portable/verify_alternate_rows.py',
        ['--old',old,'--machines',out/'variants','--output',out/'macro-diamonds.json'], alternative)
    for variant in ['row103','row157','both']:
        native = out/'variants'/variant/'k220.native.tm'
        run('window-'+variant, alternative/'portable/check_joint_fold.py',
            ['--old',old,'--new',native,'--output',out/('window-'+variant+'.json')], alternative)
        run('canonical-'+variant, alternative/'portable/canonicalize.py',
            ['--table',native,'--source',alternative/'machine/sites220.json','--output',out/'canonical-variants'/variant], alternative)
        if native.read_bytes() != (alternative/'machine'/variant/'k220.native.tm').read_bytes():
            raise ValueError('Alternative native table mismatch: '+variant)
        if (out/'canonical-variants'/variant/'k220.tm').read_bytes() != (alternative/'machine'/variant/'k220.tm').read_bytes():
            raise ValueError('Alternative canonical table mismatch: '+variant)
    run('independent-core', alternative/'verification/independent_core_audit.py',
        ['--packet',alternative,'--baseline',baseline,'--output',out/'independent-core.json'], alternative)
    for built, delivered in [('build/candidate.tm','k220.native.tm'), ('build/sites.json','sites220.json'), ('canonical/k220.tm','k220.tm')]:
        if (out/built).read_bytes() != (baseline/'machine'/delivered).read_bytes():
            raise ValueError('Baseline artifact mismatch: '+delivered)
    print('All 13 selected checks passed; rebuilt native/canonical/source bytes agree.')


if __name__ == '__main__':
    main()
