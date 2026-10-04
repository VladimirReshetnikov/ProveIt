"""Independent release-guard probes; all mutations target new review fixtures.

No science, dependency, schedule, or simulation code is executed. The genuine
reviewed release adapter/test harness are invoked only for rejection cases.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

HERE = Path(__file__).parent
SCIENCE = Path('/workspace/shared/fixed-word-invertibility61-20261004')
AUDIT = Path('/workspace/shared/audit-fixed-word-invertibility61-20261004')
RELEASE = Path('/workspace/shared/replay-fixed-word-invertibility61-20261004')


def snapshot(root):
    data = {}
    for path in [root, *sorted(root.rglob('*'))]:
        s = path.lstat()
        entry = dict(device=s.st_dev, inode=s.st_ino, mode=s.st_mode,
                     nlink=s.st_nlink, size=s.st_size, mtime_ns=s.st_mtime_ns)
        if stat.S_ISREG(s.st_mode):
            entry['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        data[str(path.relative_to(root))] = entry
    return data


before = {'science': snapshot(SCIENCE), 'audit': snapshot(AUDIT)}
(HERE / 'FROZEN_BEFORE.json').write_text(json.dumps(before, indent=2, sort_keys=True) + '\n')
release_before = snapshot(RELEASE)
work = HERE / 'probes-final'
work.mkdir(mode=0o700, exist_ok=False)
results = []


def fixture(name):
    base = work / name
    base.mkdir()
    shutil.copytree(SCIENCE, base / 'science')
    shutil.copytree(AUDIT, base / 'audit')
    return base, base / 'science', base / 'audit'


def reject(name, expected, *, science=SCIENCE, audit=AUDIT, pins=None, output=None):
    pins = RELEASE / 'PINNED_INPUTS.json' if pins is None else pins
    output = work / ('output-' + name) if output is None else output
    existed_before = os.path.lexists(output)
    command = [sys.executable, '-I', '-S', '-B', str(RELEASE / 'replay.py'),
               '--science-root', str(science), '--audit-root', str(audit),
               '--pins', str(pins), '--output-root', str(output)]
    run = subprocess.run(command, capture_output=True, timeout=60)
    passed = run.returncode == 2 and expected in run.stderr.decode()
    if not existed_before:
        passed = passed and not os.path.lexists(output)
    results.append(dict(name=name, passed=passed, returncode=run.returncode,
                        stderr=run.stderr.decode(), stdout=run.stdout.decode(),
                        output_created=not existed_before and os.path.lexists(output)))
    if not passed:
        raise RuntimeError(results[-1])


base, science, audit = fixture('missing-directory')
shutil.rmtree(science / 'dependencies')
reject('missing-directory', 'missing inventory entries', science=science, audit=audit)

base, science, audit = fixture('directory-as-file')
(science / 'README.md').unlink()
(science / 'README.md').mkdir()
reject('directory-as-file', 'unexpected directory', science=science, audit=audit)

base, science, audit = fixture('file-as-directory')
shutil.rmtree(science / 'dependencies')
(science / 'dependencies').write_bytes(b'inert fixture')
reject('file-as-directory', 'unexpected file', science=science, audit=audit)

base, science, audit = fixture('nested-directory-symlink')
(science / 'dependencies').rename(base / 'outside-dependencies')
(science / 'dependencies').symlink_to(base / 'outside-dependencies', target_is_directory=True)
reject('nested-directory-symlink', 'symbolic-link input rejected', science=science, audit=audit)

pins_copy = work / 'pins-copy.json'
pins_copy.write_bytes((RELEASE / 'PINNED_INPUTS.json').read_bytes())
pins_symlink = work / 'pins-symlink.json'
pins_symlink.symlink_to(pins_copy)
reject('pins-symlink', 'symbolic-link path rejected', pins=pins_symlink)
pins_hardlink = work / 'pins-hardlink.json'
os.link(pins_copy, pins_hardlink)
reject('pins-hardlink', 'hard-linked file rejected', pins=pins_hardlink)

parent_file = work / 'output-parent-is-file'
parent_file.write_bytes(b'inert fixture')
reject('output-parent-is-file', 'non-directory path component', output=parent_file / 'new')

dangling_output = work / 'output-dangling-link'
dangling_output.symlink_to(work / 'absent-target')
reject('output-dangling-link', 'symbolic-link path rejected', output=dangling_output)

reject('missing-output-parent', 'missing input or output parent',
       output=work / 'absent-parent' / 'new')

# Regression-check the repaired test-runner preflight on copied inputs.
# The original defect was independently reproduced in the earlier probes/
# directory: a linked work parent caused science/new-work to be created.
base, science, audit = fixture('harness-work-parent-alias')
alias = base / 'alias-to-science'
alias.symlink_to(science, target_is_directory=True)
before_copy = snapshot(science)
run = subprocess.run(
    [sys.executable, '-I', '-S', '-B', str(RELEASE / 'test_replay.py'),
     '--science-root', str(science), '--audit-root', str(audit),
     '--adapter-root', str(RELEASE), '--work-root', str(alias / 'new-work')],
    capture_output=True, timeout=60)
alias_guard_passed = (not os.path.lexists(science / 'new-work') and
                      before_copy == snapshot(science) and run.returncode != 0 and
                      b'linked or nondirectory path component' in run.stderr)
if not alias_guard_passed:
    raise RuntimeError(('alias regression failed', run.returncode, run.stderr))

optimization_output = work / 'optimized-harness-work'
optimized_run = subprocess.run(
    [sys.executable, '-I', '-S', '-B', '-O', str(RELEASE / 'test_replay.py'),
     '--science-root', str(SCIENCE), '--audit-root', str(AUDIT),
     '--adapter-root', str(RELEASE), '--work-root', str(optimization_output)],
    capture_output=True, timeout=60)
optimization_guard_passed = (optimized_run.returncode != 0 and
                             not os.path.lexists(optimization_output))
if not optimization_guard_passed:
    raise RuntimeError(('optimization guard failed', optimized_run.returncode,
                        optimized_run.stderr))

after = {'science': snapshot(SCIENCE), 'audit': snapshot(AUDIT)}
if before != after:
    raise RuntimeError('frozen inputs changed')
if release_before != snapshot(RELEASE):
    raise RuntimeError('release files changed during review probes')

report = dict(
    adapter_negative_probes=results,
    adapter_negative_probe_count=len(results),
    all_adapter_negative_probes_passed=all(row['passed'] for row in results),
    harness_work_parent_alias_regression=dict(
        passed=alias_guard_passed,
        returncode=run.returncode,
        protected_copy_new_directory=str(science / 'new-work'),
        stderr=run.stderr.decode(),
        scientific_checker_executed=False,
        consequence='The repaired test runner rejected before creating any work directory'),
    harness_optimized_invocation_guard=dict(
        passed=optimization_guard_passed,
        returncode=optimized_run.returncode,
        stderr=optimized_run.stderr.decode(),
        work_directory_created=os.path.lexists(optimization_output)),
    frozen_science_and_audit_unchanged=before == after,
    inspected_source_hashes={name: hashlib.sha256((RELEASE / name).read_bytes()).hexdigest()
                            for name in ('replay.py', 'PINNED_INPUTS.json', 'test_replay.py')},
    limits='No science code or dependency code executed; no mount changes or concurrent mutations; source-tree metadata snapshots exclude atime')
(HERE / 'PROBE_RESULTS.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
(HERE / 'FROZEN_PRESERVATION.json').write_text(json.dumps(dict(before=before, after=after), indent=2, sort_keys=True) + '\n')
print(json.dumps(dict(adapter_negative_probes=len(results),
                      alias_guard_passed=alias_guard_passed,
                      optimization_guard_passed=optimization_guard_passed,
                      frozen_inputs_unchanged=before == after), sort_keys=True))
