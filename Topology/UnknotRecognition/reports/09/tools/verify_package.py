#!/usr/bin/env python3
"""Verify the archived Git blobs, delivery hashes, and integration patch.

Uses only the standard library, plus git if present for a temporary patch
application.  It never changes a user's repository.  Missing SHA256SUMS is
reported as a build-stage omission; an existing manifest is fully verified.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]


def sha256(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    failures=[];blob_count=0;hash_count=0
    for entry in json.loads((ROOT/'data/upstream_files.json').read_text()):
        path=ROOT/'baseline/fast'/entry['path']
        data=path.read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if blob!=entry['sha'] or len(data)!=entry['size']:
            failures.append('baseline Git blob mismatch: '+entry['path'])
        blob_count+=1
    manifest=ROOT/'SHA256SUMS'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest,name=line.split('  ',1);path=ROOT/name
            if not path.is_file() or sha256(path)!=digest:
                failures.append('deliverable hash mismatch: '+name)
            hash_count+=1
    initial=json.loads((ROOT/'data/paired_benchmarks.json').read_text())
    for name,digest in initial['source_sha256'].items():
        if name.startswith('baseline/'):
            path=ROOT/name
        else:
            path=ROOT/'data/benchmark_sources/initial'/Path(name).relative_to('fast')
        if not path.is_file() or sha256(path)!=digest:
            failures.append('initial benchmark source mismatch: '+name)
    final=ROOT/'data/reduced_benchmark_final.json'
    if final.exists():
        p=json.loads(final.read_text())['provenance']
        for name,digest in p['source_sha256'].items():
            path=final.parent/p['snapshot_directory_relative_to_output']/name
            if not path.is_file() or sha256(path)!=digest:
                failures.append('pointed benchmark snapshot mismatch: '+name)
    paired_final=ROOT/'data/paired_benchmarks_final.json'
    if paired_final.exists():
        record=json.loads(paired_final.read_text())
        snapshot=paired_final.parent/record['provenance']['snapshot_directory_relative_to_data']
        for name,digest in record['source_sha256'].items():
            path=ROOT/name if name.startswith('baseline/') else snapshot/name
            if not path.is_file() or sha256(path)!=digest:
                failures.append('final paired benchmark snapshot mismatch: '+name)
    patch=ROOT/'integration/fastunknot-0.3.patch'
    patch_result='git unavailable; skipped'
    if shutil.which('git'):
        with tempfile.TemporaryDirectory(prefix='unknot_patch_check_') as temp:
            root=Path(temp);dest=root/'Topology/UnknotRecognition/fast'
            shutil.copytree(ROOT/'baseline/fast',dest,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
            check=subprocess.run(['git','apply','--check',str(patch)],cwd=root,text=True,capture_output=True)
            if check.returncode:failures.append('patch check: '+check.stderr)
            else:
                apply=subprocess.run(['git','apply',str(patch)],cwd=root,text=True,capture_output=True)
                if apply.returncode:failures.append('patch apply: '+apply.stderr)
                else:
                    for source in (ROOT/'fast').rglob('*'):
                        if not source.is_file() or '__pycache__' in source.parts or source.suffix=='.pyc':continue
                        target=dest/source.relative_to(ROOT/'fast')
                        if not target.is_file() or target.read_bytes()!=source.read_bytes():
                            failures.append('patched output mismatch: '+str(source.relative_to(ROOT)))
                    patch_result='applies cleanly and reproduces updated fast tree'
    report={'archived_git_blobs_checked':blob_count,'delivery_hashes_checked':hash_count,
            'manifest_present':manifest.exists(),'patch':patch_result,'failures':failures,
            'status':'passed' if not failures else 'failed'}
    print(json.dumps(report,indent=2))
    if failures:raise SystemExit(1)


if __name__=='__main__':main()
