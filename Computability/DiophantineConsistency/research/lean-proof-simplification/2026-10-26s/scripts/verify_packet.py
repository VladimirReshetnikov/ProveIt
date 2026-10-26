#!/usr/bin/env python3
"""Verify packet integrity, source metrics, and optional pinned applicability."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
from validate import BUNDLE, PIN, head, sha

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path)
    args = ap.parse_args()
    checksums = BUNDLE/'SHA256SUMS'
    checked = 0
    if checksums.exists():
        for line in checksums.read_text().splitlines():
            digest, rel = line.split('  ',1)
            path = (BUNDLE/rel).resolve()
            assert path.is_relative_to(BUNDLE), rel
            assert sha(path) == digest, rel
            checked += 1
    entries = json.loads((BUNDLE/'evidence/source-manifest.json').read_text())['files']
    for row in entries:
        path = BUNDLE/'candidates'/row['path']
        data = path.read_bytes()
        assert hashlib.sha256(data).hexdigest() == row['after_sha256'], row['path']
        assert len(data) == row['after_bytes']
        assert len(data.splitlines()) == row['after_lines']
    metrics = json.loads((BUNDLE/'evidence/summary-metrics.json').read_text())
    raw = sum(x['before_lines']-x['after_lines'] for x in entries)
    assert raw == metrics['raw_lines_saved']
    assert raw-metrics['prior_alias_cleanup_lines'] == metrics['incremental_lines_saved']
    if args.repo:
        repo = args.repo.resolve()
        assert head(repo) == PIN
        for row in entries:
            path = repo/row['path']
            if row['new_file']: assert not path.exists(), row['path']
            else: assert sha(path) == row['before_sha256'], row['path']
        subprocess.run(['git','-C',str(repo),'apply','--check',str(BUNDLE/'patches/combined.patch')],check=True)
    print(f'PASS: {checked} integrity hashes, {len(entries)} candidate source files; '
          f'{raw} raw lines and {metrics["incremental_lines_saved"]} incremental lines saved.')

if __name__ == '__main__': main()
