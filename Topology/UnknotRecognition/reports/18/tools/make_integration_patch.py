"""Build and check the additive patch against the packaged pinned fast tree.

Only textual source, tests, and documentation are included. Python bytecode
and cache directories are excluded. Verification applies the patch inside
the actual target directory layout and compares the complete resulting tree.
This is an application check, not another regression-suite execution.
"""
from __future__ import annotations

import difflib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TARGET = Path('Topology/UnknotRecognition/fast')
BASELINE = 'ea2abcb115aaa58f0b193ce1e045c2def983e1e6'


def files(root: Path) -> dict[str, Path]:
    return {
        path.relative_to(root).as_posix(): path
        for path in root.rglob('*')
        if path.is_file() and '__pycache__' not in path.parts
        and path.suffix not in {'.pyc', '.pyo'}
        and '.pytest_cache' not in path.parts
    }


def checked(command: list[str], cwd: Path):
    answer = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if answer.returncode:
        raise RuntimeError(f'{command!r} failed:\n{answer.stdout}{answer.stderr}')


def main():
    old = files(ROOT / 'reference' / 'fast')
    new = files(ROOT / 'fast')
    if set(old) - set(new):
        raise RuntimeError('the integration patch must not remove baseline files')
    if old['LICENSE'].read_bytes() != new['LICENSE'].read_bytes():
        raise RuntimeError('the baseline MIT-0 license must remain unchanged')
    chunks = []
    changes = []
    for name in sorted(new):
        before = old[name].read_bytes() if name in old else b''
        after = new[name].read_bytes()
        if before == after:
            continue
        chunks.append(f'diff --git a/{name} b/{name}\n')
        if name not in old:
            chunks.append('new file mode 100644\n')
        chunks.extend(difflib.unified_diff(
            before.decode('utf-8').splitlines(keepends=True),
            after.decode('utf-8').splitlines(keepends=True),
            fromfile=f'a/{name}' if name in old else '/dev/null',
            tofile=f'b/{name}', n=3,
        ))
        changes.append({'path': name, 'change': 'modified' if name in old else 'added'})
    patch = ROOT / 'integration.patch'
    patch.write_text(''.join(chunks), encoding='utf-8')
    with tempfile.TemporaryDirectory(prefix='unknot-patch-check-') as temporary:
        temp_root = Path(temporary)
        target = temp_root / TARGET
        shutil.copytree(ROOT / 'reference' / 'fast', target,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc', '*.pyo', '.pytest_cache'))
        checked(['git', 'init', '--quiet'], temp_root)
        options = [f'--directory={TARGET.as_posix()}', str(patch)]
        checked(['git', 'apply', '--check', *options], temp_root)
        checked(['git', 'apply', *options], temp_root)
        applied = files(target)
        if set(applied) != set(new):
            raise RuntimeError('patched file list differs from delivered fast tree')
        for name in sorted(new):
            if applied[name].read_bytes() != new[name].read_bytes():
                raise RuntimeError(f'patched bytes differ: {name}')
    result = {
        'baseline_revision': BASELINE,
        'patch': 'integration.patch',
        'target_directory': TARGET.as_posix(),
        'changed_files': changes,
        'added_count': sum(item['change'] == 'added' for item in changes),
        'modified_count': sum(item['change'] == 'modified' for item in changes),
        'removed_count': 0,
        'baseline_license_preserved': True,
        'git_apply_check': 'passed',
        'git_apply': 'passed',
        'complete_patched_tree_comparison': 'byte-identical to delivered fast tree',
        'tests_rerun': False,
    }
    (ROOT / 'results' / 'patch_check.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
