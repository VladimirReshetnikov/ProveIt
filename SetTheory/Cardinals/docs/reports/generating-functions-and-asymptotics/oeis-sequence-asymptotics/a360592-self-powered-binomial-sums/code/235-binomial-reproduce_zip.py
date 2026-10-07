#!/usr/bin/env python3
"""Rebuild an actual Report235 ZIP under normal and optimized Python.

Two independently extracted source trees must remain byte-identical to the
archive. Both rebuilt ZIPs (all members and metadata), PDFs and receipts must
match the original and each other. No source-tree output or network is used.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
sys.dont_write_bytecode = True
import zipfile
from common import ROOT, emit, new_file_path, require

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def archive_contents(path):
    require(path.is_file() and not path.is_symlink(), 'archive must be a regular nonsymlink file')
    contents = {}
    metadata = {}
    with zipfile.ZipFile(path) as archive:
        members = archive.infolist()
        require(1 <= len(members) <= 500, 'invalid archive member count')
        require(sum(info.file_size for info in members) <= 32 * 1024 * 1024, 'archive exceeds 32 MiB')
        for info in members:
            name = info.filename
            require(name.startswith('Report235/'), 'invalid archive top-level directory')
            relative = name[len('Report235/'):]
            require(relative and '\\' not in relative and not relative.startswith('/'), 'invalid ZIP path')
            require(all(part not in ('', '.', '..') for part in relative.split('/')), 'invalid ZIP component')
            require(not info.is_dir(), 'archive directory records are not part of this deterministic format')
            require(relative not in contents, 'duplicate ZIP member')
            require(stat.S_ISREG(info.external_attr >> 16), 'nonregular ZIP member')
            require(info.compress_type == zipfile.ZIP_STORED, 'archive must use stored members')
            contents[relative] = archive.read(info)
            metadata[relative] = {'timestamp': list(info.date_time), 'mode': info.external_attr >> 16,
                                  'compression': info.compress_type, 'creator': info.create_system}
    require('build.py' in contents and 'MANIFEST.sha256' in contents, 'missing build or manifest')
    return contents, metadata


def tree_bytes(root):
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'unexpected source symlink')
        if path.is_file():
            result[path.relative_to(root).as_posix()] = path.read_bytes()
        else:
            require(path.is_dir(), 'unexpected source entry')
    return result


def run_build(source, destination, optimized, log):
    env = os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONINTMAXSTRDIGITS='640', PYTHONHASHSEED='0')
    command = [sys.executable, '-B'] + (['-O'] if optimized else [])
    command += [str(source / 'build.py'), '--output-dir', str(destination)]
    result = subprocess.run(command, cwd=source, env=env, capture_output=True, check=False)
    log.write_bytes(result.stdout + result.stderr)
    require(result.returncode == 0, 'rebuild failed; inspect ' + str(log))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', required=True)
    parser.add_argument('--output-dir', required=True, help='new directory outside the source package')
    args = parser.parse_args()
    out = new_file_path(args.output_dir)
    original = Path(args.archive)
    contents, metadata = archive_contents(original)
    original_bytes = original.read_bytes()
    # Never execute build code merely because an untrusted ZIP supplies it.
    require(contents == tree_bytes(ROOT), 'archive members differ from this trusted frozen package')
    # Exclusive creation follows validation; extraction uses only validated names.
    out.mkdir(exist_ok=False)
    paths = {}
    for mode in ('normal', 'optimized'):
        source = out / (mode + '_source')
        source.mkdir()
        for name, data in contents.items():
            target = source / name
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as handle:
                handle.write(data)
        require(tree_bytes(source) == contents, 'extracted source differs from archive')
        destination = out / (mode + '_build')
        run_build(source, destination, mode == 'optimized', out / (mode + '.log'))
        require(tree_bytes(source) == contents, 'extracted source changed during rebuild')
        rebuilt = destination / 'Report235.zip'
        rebuilt_contents, rebuilt_metadata = archive_contents(rebuilt)
        require(rebuilt_contents == contents, 'rebuilt archive members differ')
        require(rebuilt_metadata == metadata, 'rebuilt archive metadata differs')
        require(rebuilt.read_bytes() == original_bytes, 'rebuilt ZIP bytes differ from original')
        require((destination / 'Report235.pdf').read_bytes() == contents['Report235.pdf'], 'PDF differs')
        require((destination / 'exact_checks.json').read_bytes() == contents['code/receipt.json'], 'code receipt differs')
        require((destination / 'numerical_checks.json').read_bytes() == contents['code/numerical_receipt.json'], 'numerical receipt differs')
        require((destination / 'guard_checks.json').read_bytes() == contents['code/guard_receipt.json'], 'guard receipt differs')
        paths[mode] = destination
    for name in ('Report235.pdf', 'Report235.zip', 'exact_checks.json', 'numerical_checks.json', 'guard_checks.json', 'build_checks.json'):
        require((paths['normal'] / name).read_bytes() == (paths['optimized'] / name).read_bytes(),
                'normal and optimized outputs differ: ' + name)
    require(original.read_bytes() == original_bytes, 'input archive changed')
    require(tree_bytes(ROOT) == contents, 'trusted source package changed')
    receipt = {'status': 'PASS', 'normal_and_optimized_identical': True,
               'actual_input_zip_sha256': sha(original_bytes), 'zip_members': len(contents),
               'every_member_bytes_and_metadata_match': True,
               'source_trees_unchanged': True, 'trusted_source_unchanged': True, 'input_archive_unchanged': True,
               'output_sha256': {name: sha((paths['normal'] / name).read_bytes())
                                 for name in ('Report235.pdf', 'Report235.zip', 'exact_checks.json', 'numerical_checks.json', 'guard_checks.json', 'build_checks.json')},
               'member_sha256': {name: sha(data) for name, data in contents.items()},
               'scope': 'Byte reproducibility on the installed toolchain; the manifest is an integrity record, not a digital signature.'}
    # Output directory was exclusively created above; no preexisting file is reused.
    with (out / 'reproduction_checks.json').open('x', encoding='utf-8', newline='\n') as handle:
        handle.write(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    emit(receipt)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError, zipfile.BadZipFile) as exc:
        raise SystemExit(str(exc))
