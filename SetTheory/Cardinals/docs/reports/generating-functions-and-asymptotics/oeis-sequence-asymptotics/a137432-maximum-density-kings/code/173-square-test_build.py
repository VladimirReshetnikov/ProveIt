#!/usr/bin/env python3
"""Bounded standard-library tests of Report173 packaging invariants."""
from pathlib import Path
import json
import sys
import tempfile
import zipfile
sys.dont_write_bytecode = True
import build
import verify_package

def expect_error(function, message):
    try:
        function()
    except (build.BuildError, ValueError, OSError):
        return
    raise RuntimeError('missing expected rejection: ' + message)

def run_tests():
    build.validate_sources()
    with tempfile.TemporaryDirectory(prefix='report173-package-test-') as temp:
        root = Path(temp)
        src = root / 'src'; src.mkdir()
        build.write_new(src / 'a.txt', b'A\n')
        (src / 'nested').mkdir(); build.write_new(src / 'nested' / 'b.txt', b'B\n')
        build.write_new(src / 'SHA256SUMS.json', build.json_bytes(build.manifest(src)))
        if verify_package.verify(src) != 2:
            raise RuntimeError('manifest count mismatch')
        first, second = root / 'first.zip', root / 'second.zip'
        build.make_zip(src, first); build.make_zip(src, second)
        if first.read_bytes() != second.read_bytes():
            raise RuntimeError('archive bytes are nondeterministic')
        expect_error(lambda: build.make_zip(src, first), 'existing ZIP')
        expect_error(lambda: build.write_new(src / 'a.txt', b'changed'), 'existing file')
        expect_error(lambda: build.build(first), 'existing build output')
        dest = root / 'extracted'; dest.mkdir()
        with zipfile.ZipFile(first) as z:
            z.extractall(dest)
        verify_package.verify(dest)
        (dest / 'a.txt').write_bytes(b'tamper')
        expect_error(lambda: verify_package.verify(dest), 'tampered contents')
        (dest / 'a.txt').write_bytes(b'A\n'); (dest / 'extra').write_bytes(b'extra')
        expect_error(lambda: verify_package.verify(dest), 'extra file')
        (src / 'link').symlink_to(src / 'a.txt')
        expect_error(lambda: build.make_zip(src, root / 'symlink.zip'), 'symlink source')
    return {'status': 'PASS', 'checks': ['source_allowlist', 'manifest_integrity',
        'deterministic_zip', 'zip_no_clobber', 'file_no_clobber', 'build_no_clobber',
        'extracted_verification', 'tamper_detection', 'extra_file_detection', 'symlink_rejection']}

if __name__ == '__main__':
    print(json.dumps(run_tests(), sort_keys=True, indent=2))
