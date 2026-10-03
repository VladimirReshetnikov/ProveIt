#!/usr/bin/env python3
"""Adversarial tests of the outer release inventory and article-review binding."""
import sys
sys.dontwritebytecode = True
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import verify_release as v


def seal(root):
    state = v.snapshot(root)
    state['files'] = {k: d for k, d in state['files'].items() if k not in v.SEALS}
    data = (json.dumps(state, indent=2, sort_keys=True) + '\n').encode()
    (root / 'RELEASE_INVENTORY.json').write_bytes(data)
    (root / 'RELEASE_INVENTORY.sha256').write_text(hashlib.sha256(data).hexdigest() + '\n')


def append(root, name):
    p = root / name
    p.write_bytes(p.read_bytes() + b'\n')


def changed_review_binding(root):
    append(root, 'article/report24.tex')
    seal(root)


def changed_render_binding(root):
    append(root, 'article/report24.pdf')
    seal(root)


def main():
    before = v.snapshot(v.ROOT)
    v.integrity()
    cases = (
        ('missing_pdf', lambda r: (r / 'article/report24.pdf').unlink()),
        ('altered_tex', lambda r: append(r, 'article/report24.tex')),
        ('altered_checker', lambda r: append(r, 'reproducibility/checks/check_native_law.py')),
        ('missing_inventory', lambda r: (r / 'RELEASE_INVENTORY.json').unlink()),
        ('altered_digest', lambda r: append(r, 'RELEASE_INVENTORY.sha256')),
        ('extra_file', lambda r: (r / 'unlisted.txt').write_text('unlisted')),
        ('extra_directory', lambda r: (r / 'unlisted').mkdir()),
        ('symlink', lambda r: (r / 'unlisted').symlink_to('article/report24.tex')),
        ('stale_math_review_after_reseal', changed_review_binding),
        ('stale_render_review_after_reseal', changed_render_binding),
    )
    results = []
    with tempfile.TemporaryDirectory(prefix='report24-mutations-') as work:
        for index, (name, mutate) in enumerate(cases):
            root = Path(work) / str(index)
            shutil.copytree(v.ROOT, root)
            mutate(root)
            try:
                v.integrity(root)
            except (ValueError, KeyError, OSError, json.JSONDecodeError):
                results.append({'test': name, 'status': 'PASS'})
            else:
                raise RuntimeError('Mutation accepted: ' + name)
    v.need(v.snapshot(v.ROOT) == before, 'Release changed during mutation testing')
    print(json.dumps({'status': 'PASS', 'tests': results, 'test_count': len(results),
                      'python_optimized': bool(sys.flags.optimize),
                      'exact_inventory_unchanged': True}, indent=2))


if __name__ == '__main__':
    main()
