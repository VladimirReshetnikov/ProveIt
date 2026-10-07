#!/usr/bin/env python3
"""Deliberate malformed-package tests; failures must persist under python -O."""
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('report_package', ROOT/'reproduce.py')
pkg = importlib.util.module_from_spec(spec); spec.loader.exec_module(pkg)


def reject(fn, label, records):
    try:
        fn()
    except (RuntimeError, ValueError, FileNotFoundError, zipfile.BadZipFile):
        records.append(label)
    else:
        raise RuntimeError('negative control accepted: ' + label)


def main():
    records = []
    reject(lambda: pkg.require(False, 'intentional'), 'explicit exception guard', records)
    for bad in ['', '.', '..', '../x', '/absolute', 'a/../b', 'a//b', 'a/./b', 'a\\b']:
        reject(lambda b=bad: pkg.safe_name(b), 'unsafe path ' + repr(bad), records)
    with tempfile.TemporaryDirectory(prefix='report216-guards-') as tmp:
        base = Path(tmp); root = base/'Report216'; root.mkdir()
        (root/'reproduce.py').write_text('pass\n')
        (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\n')
        pkg.require(pkg.source_names(root) == ['SOURCE_FILES.txt', 'reproduce.py'], 'positive inventory control')
        existing = base/'existing'; existing.mkdir()
        reject(lambda: pkg.validate_output(existing, root), 'existing output', records)
        reject(lambda: pkg.validate_output(root/'new', root), 'descendant output', records)
        reject(lambda: pkg.validate_output(base/'missing'/'new', root), 'missing output parent', records)
        linked = base/'linked'; linked.symlink_to(existing, target_is_directory=True)
        reject(lambda: pkg.validate_output(linked, root), 'symbolic output', records)
        inventory = root/'SOURCE_FILES.txt'; good = inventory.read_text()
        inventory.write_text(good+'reproduce.py\n')
        reject(lambda: pkg.source_names(root), 'duplicate inventory', records)
        inventory.write_text(good+'absent.py\n')
        reject(lambda: pkg.source_names(root), 'missing source', records)
        inventory.write_text(good+'Report216.pdf\n')
        reject(lambda: pkg.source_names(root), 'reserved PDF inventory', records)
        inventory.write_text(good)
        (root/'unexpected.txt').write_text('unexpected')
        reject(lambda: pkg.source_names(root), 'unlisted file', records)
        (root/'unexpected.txt').unlink()
        (root/'linked.txt').symlink_to(root/'reproduce.py')
        reject(lambda: pkg.source_names(root), 'linked package member', records)
        (root/'linked.txt').unlink()
        (root/'reproduce.py').write_text('assert True\n')
        reject(lambda: pkg.source_names(root), 'assert guard disabled by optimization', records)
        (root/'reproduce.py').write_text('pass\n')
        (root/pkg.PDF).write_bytes(b'PDF positive fixture\n')
        names = ['SOURCE_FILES.txt', 'reproduce.py', pkg.PDF]
        good_manifest = {'format': pkg.FORMAT, 'files': {n: pkg.sha((root/n).read_bytes()) for n in names}}
        pkg.write_json(root/pkg.MANIFEST, good_manifest)
        pkg.verify_manifest(root, names)
        (root/pkg.MANIFEST).write_text('{"format":"x","format":"y","files":{}}')
        reject(lambda: pkg.verify_manifest(root, names), 'duplicate manifest key', records)
        altered = json.loads(json.dumps(good_manifest)); altered['files'][pkg.PDF] = '0'*64
        pkg.write_json(root/pkg.MANIFEST, altered)
        reject(lambda: pkg.verify_manifest(root, names), 'false manifest digest', records)
        pkg.write_json(root/pkg.MANIFEST, good_manifest)
        (root/pkg.PDF).write_bytes(b'changed PDF\n')
        reject(lambda: pkg.verify_manifest(root, names), 'tampered source byte', records)
        (root/pkg.PDF).write_bytes(b'PDF positive fixture\n')
        members = sorted(names+[pkg.MANIFEST]); archive = base/'good.zip'
        pkg.archive(root, members, archive)
        pkg.verify_zip(root, members, archive)
        with zipfile.ZipFile(base/'bad.zip', 'w') as z:
            z.writestr('Report216/unexpected.txt', b'unexpected')
        reject(lambda: pkg.verify_zip(root, members, base/'bad.zip'), 'wrong actual ZIP inventory', records)
        with zipfile.ZipFile(base/'poison.zip', 'w') as z:
            for name in members:
                z.writestr('Report216/'+name, b'poison' if name == pkg.PDF else (root/name).read_bytes())
        reject(lambda: pkg.verify_zip(root, members, base/'poison.zip'), 'wrong actual ZIP member bytes', records)
        reject(lambda: pkg.archive(root, list(reversed(members)), base/'unsorted.zip'), 'unsorted ZIP inventory', records)
    print(json.dumps({'status': 'PASS', 'negative_controls': records, 'count': len(records),
                      'positive_controls': ['inventory', 'manifest', 'actual ZIP'],
                      'note': 'Functional guards, not a security audit; explicit exceptions remain active under -O.'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
