#!/usr/bin/env python3
"""Rebuild an actual Report241 ZIP under normal and optimized Python.

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
from common import ROOT, ARTIFACT_STEM, REPORT_NUMBER, emit, new_file_path, require
sys.path.insert(0, str(ROOT))
import build as frozen_build

RECEIPTS=('count_receipt.json','construction_receipt.json','upper_bound_receipt.json','guard_receipt.json')
OUTPUTS=(ARTIFACT_STEM+'.pdf',ARTIFACT_STEM+'.zip')+RECEIPTS+('build_checks.json',)

if not hasattr(sys, 'set_int_max_str_digits'):
    raise RuntimeError('Python 3.11 or newer is required')
sys.set_int_max_str_digits(640)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def archive_contents(path):
    require(isinstance(path,Path), 'archive path must be pathlib.Path')
    require(path.is_file() and not path.is_symlink(), 'archive must be a regular nonsymlink file')
    require(not any(p.is_symlink() for p in path.parents), 'archive path has a symlink ancestor')
    contents = {}
    metadata = {}
    require(path.stat().st_size <= 33*1024*1024, 'archive file exceeds 33 MiB')
    with zipfile.ZipFile(path) as archive:
        require(archive.comment == b'', 'archive comment forbidden')
        members = archive.infolist()
        require(1 <= len(members) <= 500, 'invalid archive member count')
        require(sum(info.file_size for info in members) <= 32 * 1024 * 1024, 'archive exceeds 32 MiB')
        for info in members:
            name = info.filename
            require(name == info.orig_filename and all(32 <= ord(c) <= 126 for c in name),
                    'noncanonical or non-ASCII ZIP member name')
            require(name.startswith(ARTIFACT_STEM+'/'), 'invalid archive top-level directory')
            relative = name[len(ARTIFACT_STEM+'/'):]
            require(relative and '\\' not in relative and not relative.startswith('/'), 'invalid ZIP path')
            require(all(part not in ('', '.', '..') for part in relative.split('/')), 'invalid ZIP component')
            require(not info.is_dir(), 'archive directory records are not part of this deterministic format')
            require(relative not in contents, 'duplicate ZIP member')
            require(stat.S_ISREG(info.external_attr >> 16), 'nonregular ZIP member')
            require(info.compress_type == zipfile.ZIP_STORED, 'archive must use stored members')
            require(info.date_time == (2026,10,5,0,0,0), 'unexpected member timestamp')
            require(info.external_attr == 0o100644 << 16 and info.create_system == 3,
                    'unexpected member mode or creator')
            require(info.extra == b'' and info.comment == b'' and info.flag_bits == 0,
                    'unexpected member extra metadata')
            contents[relative] = archive.read(info)
            metadata[relative] = {'timestamp': list(info.date_time), 'mode': info.external_attr >> 16,
                                  'compression': info.compress_type, 'creator': info.create_system,
                                  'flags':info.flag_bits,'extra':info.extra.hex(),'comment':info.comment.hex(),
                                  'CRC':info.CRC,'file_size':info.file_size,'compressed_size':info.compress_size,
                                  'internal_attr':info.internal_attr,'create_version':info.create_version,
                                  'extract_version':info.extract_version,'volume':info.volume,
                                  'header_offset':info.header_offset}
    require('build.py' in contents and 'MANIFEST.sha256' in contents, 'missing build or manifest')
    return contents, metadata


def _tree_bytes(root):
    result = {}
    for path in sorted(root.rglob('*')):
        require(not path.is_symlink(), 'unexpected source symlink')
        if path.is_file():
            result[path.relative_to(root).as_posix()] = path.read_bytes()
        else:
            require(path.is_dir(), 'unexpected source entry')
    return result


def _run_build(source, destination, optimized, log):
    env = os.environ.copy()
    env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONINTMAXSTRDIGITS='640', PYTHONHASHSEED='0', PYTHONOPTIMIZE='0')
    command = [sys.executable, '-B', '-X', 'int_max_str_digits=640'] + (['-O'] if optimized else [])
    command += [str(source / 'build.py'), '--output-dir', str(destination)]
    result = subprocess.run(command, cwd=source, env=env, capture_output=True, check=False, timeout=900)
    with log.open('xb') as handle:handle.write(result.stdout + result.stderr)
    require(result.returncode == 0, 'rebuild failed; inspect ' + str(log))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', required=True)
    parser.add_argument('--output-dir', required=True, help='new directory outside the source package')
    args = parser.parse_args()
    out = new_file_path(args.output_dir)
    original = Path(args.archive)
    frozen_build.verify()
    trusted_inventory = frozen_build.inventory()
    contents, metadata = archive_contents(original)
    original_bytes = original.read_bytes()
    # Never execute build code merely because an untrusted ZIP supplies it.
    require(contents == _tree_bytes(ROOT), 'archive members differ from this trusted frozen package')
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
        require(_tree_bytes(source) == contents, 'extracted source differs from archive')
        destination = out / (mode + '_build')
        _run_build(source, destination, mode == 'optimized', out / (mode + '.log'))
        require(_tree_bytes(source) == contents, 'extracted source changed during rebuild')
        require({p.name for p in destination.iterdir() if p.is_file()} == set(OUTPUTS),
                'unexpected or missing top-level build output')
        require({p.name for p in destination.iterdir() if p.is_dir()} == {'logs'},
                'unexpected top-level build directory')
        rebuilt = destination / (ARTIFACT_STEM+'.zip')
        rebuilt_contents, rebuilt_metadata = archive_contents(rebuilt)
        require(rebuilt_contents == contents, 'rebuilt archive members differ')
        require(rebuilt_metadata == metadata, 'rebuilt archive metadata differs')
        require(rebuilt.read_bytes() == original_bytes, 'rebuilt ZIP bytes differ from original')
        require((destination / (ARTIFACT_STEM+'.pdf')).read_bytes() == contents[ARTIFACT_STEM+'.pdf'], 'PDF differs')
        for name in RECEIPTS:
            require((destination/name).read_bytes()==contents['code/'+name], 'receipt differs: '+name)
        paths[mode] = destination
    for name in OUTPUTS:
        require((paths['normal'] / name).read_bytes() == (paths['optimized'] / name).read_bytes(),
                'normal and optimized outputs differ: ' + name)
    require(original.read_bytes() == original_bytes, 'input archive changed')
    require(_tree_bytes(ROOT) == contents, 'trusted source package changed')
    require(frozen_build.inventory() == trusted_inventory, 'trusted source inventory changed')
    receipt = {'status': 'PASS', 'report_number': REPORT_NUMBER, 'normal_and_optimized_identical': True,
               'actual_input_zip_sha256': sha(original_bytes), 'zip_members': len(contents),
               'every_member_bytes_and_metadata_match': True,
               'seven_top_level_output_files_checked': True, 'source_trees_unchanged': True, 'trusted_source_unchanged': True, 'input_archive_unchanged': True,
               'output_sha256': {name: sha((paths['normal'] / name).read_bytes())
                                 for name in OUTPUTS},
               'member_sha256': {name: sha(data) for name, data in contents.items()},
               'scope': 'Byte reproducibility on the installed toolchain; the manifest is an integrity record, not a digital signature.'}
    # Output directory was exclusively created above; no preexisting file is reused.
    with (out / 'reproduction_checks.json').open('x', encoding='utf-8', newline='\n') as handle:
        handle.write(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    emit(receipt)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, ArithmeticError, zipfile.BadZipFile, subprocess.TimeoutExpired) as exc:
        raise SystemExit(str(exc))
