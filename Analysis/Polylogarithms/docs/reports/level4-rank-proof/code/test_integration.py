#!/usr/bin/env python3
"""Test the integration helper against synthetic local fixtures only."""
from __future__ import annotations
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    if not __debug__:
        raise RuntimeError('Do not use -O for this test.')
    spec = importlib.util.spec_from_file_location('integration_fixture',
                                                 ROOT/'integration/apply_integration.py')
    if spec is None or spec.loader is None:
        raise RuntimeError('Could not load the integration helper.')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    checks = []
    # Standard Git empty-blob object id, not a plain file SHA-1.
    assert helper.git_blob_sha1(b'') == 'e69de29bb2d1d6434b8b29ae775ad8c2e48c5391'
    checks.append('Git empty-blob hash matches the known object id')
    with tempfile.TemporaryDirectory() as temp:
        repo = Path(temp)
        target = repo/helper.TARGET
        target.parent.mkdir(parents=True)
        original = ('before\n'+helper.ANCHOR+'\nold rank subsection\n').encode()
        target.write_bytes(original)
        try:
            helper.prepare(repo)
        except ValueError:
            checks.append('Changed source rejected')
        else:
            raise AssertionError('Changed source accepted')
        assert target.read_bytes() == original
        # Only this in-memory module copy is changed to admit a synthetic fixture.
        helper.EXPECTED_BLOB = helper.git_blob_sha1(original)
        _, destination, replacement, fragment = helper.prepare(repo)
        assert target.read_bytes() == original and not destination.exists()
        assert replacement == b'before\n\\input{chapters/05-level4-rank}\n'
        assert fragment == (ROOT/'integration/05-level4-rank.tex').read_bytes()
        checks.append('Dry-run preparation is nonmutating and preserves the prefix')
        oldargv = sys.argv
        try:
            sys.argv = ['apply_integration.py', str(repo), '--apply']
            with contextlib.redirect_stdout(io.StringIO()):
                assert helper.main() == 0
        finally:
            sys.argv = oldargv
        assert target.read_bytes() == replacement
        assert destination.read_bytes() == fragment
        checks.append('Opt-in synthetic integration writes exact expected bytes')
        try:
            helper.prepare(repo)
        except ValueError:
            checks.append('Repeat on changed canonical target refused')
        else:
            raise AssertionError('Changed canonical target accepted')
        target.write_bytes(original)
        try:
            helper.prepare(repo)
        except FileExistsError:
            checks.append('Existing destination fragment is not overwritten')
        else:
            raise AssertionError('Existing destination was accepted')
    report = dict(status='PASS', scope='synthetic local fixtures only; no repository modified',
                  checks=checks)
    (ROOT/'data/integration_helper_checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
