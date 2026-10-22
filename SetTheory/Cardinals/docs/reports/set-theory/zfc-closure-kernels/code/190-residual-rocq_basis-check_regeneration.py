#!/usr/bin/env python3
"""Apply the review overlay only to a private copy, then audit all generated files."""
import argparse
import hashlib
import json
import shutil
import subprocess
import time
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--reference', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    a = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = a.out.resolve()
    if out.exists():
        raise SystemExit('Output must be new; no existing tree is overwritten.')
    out.mkdir(parents=True)
    rel = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
    source = a.repo.resolve() / rel
    baseline = source / 'rocq/rocq-extension/coq/215'
    for name in ['CD222.v', 'DomRho8.v']:
        if sha(baseline / name) != sha(root / 'inputs/K215F' / name):
            raise SystemExit('Source differs from the reviewed baseline: ' + name)
    check = subprocess.run(['git', '-C', str(a.repo.resolve()), 'apply', '--check',
                            str(root / 'integration.patch')], capture_output=True, text=True)
    if check.returncode:
        raise SystemExit(check.stdout + check.stderr)
    stage = out / 'k225-formal'
    shutil.copytree(source, stage,
                    ignore=shutil.ignore_patterns('verification', 'receipts', 'toolchain', '__pycache__'))
    overlay = root / 'integration-overlay' / rel
    for path in overlay.rglob('*'):
        if path.is_file():
            target = stage / path.relative_to(overlay)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    generated = out / 'generated/215'
    command = ['python3', '-B', str(stage / 'rocq/rocq-extension/regenerate215.py'),
               '--reference', str(a.reference.resolve()), '--output', str(generated)]
    start = time.monotonic()
    run = subprocess.run(command, capture_output=True, text=True)
    seconds = time.monotonic() - start
    (out / 'regeneration.log').write_text(run.stdout + run.stderr)
    if run.returncode:
        raise SystemExit(run.stdout + run.stderr)
    changed = [f.name for f in sorted(baseline.glob('*.v')) if sha(f) != sha(generated / f.name)]
    added = [f.name for f in sorted(generated.glob('*.v')) if not (baseline / f.name).exists()]
    if changed != ['CD222.v', 'DomRho8.v'] or added != ['DominatedImplication.v']:
        raise SystemExit('Unexpected regenerated differences: ' + repr((changed, added)))
    for name in changed + added:
        if sha(generated / name) != sha(root / 'candidate/K215F' / name):
            raise SystemExit('Regeneration differs from checked candidate: ' + name)
    manifest = json.loads((stage / 'rocq/rocq-extension/manifest.json').read_text())
    order = manifest['variants']['215']['compile_order']
    if len(order) != 43 or order.index('DominatedImplication') >= order.index('CD222'):
        raise SystemExit('Compile-order registration failed.')
    for name in changed + added:
        if manifest['files']['coq/215/' + name] != sha(generated / name):
            raise SystemExit('Source manifest binding failed: ' + name)
    result = {'status': 'PASS_REGENERATION_EXACT_DIFF', 'command': command,
              'seconds': seconds, 'generated_count': 43, 'unchanged_count': 40,
              'changed': changed, 'added': added, 'patch_applies': True,
              'source_sha256': {f.name: sha(f) for f in sorted(generated.glob('*.v'))},
              'endpoint_built': False}
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], '40 unchanged, 2 replacements, 1 generic module')


if __name__ == '__main__':
    main()
