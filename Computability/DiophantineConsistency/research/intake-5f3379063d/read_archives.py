#!/usr/bin/env python3
"""Inert, read-only ZIP inventory; never imports or executes an archive member."""
import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
COMMIT = '5f3379063df18910a981d2e6cae6aee91b79cf4d'
NAMES = [
    'ConZFC_Cofinal_Witnesses_2026-10-24.zip',
    'ConZFC_Height_One_and_Degree_464_2026-10-24.zip',
    'ConZFC_Paired_Guards_Centered_Carriers_2026-10-24.zip',
    'ConZFC_Residue_Compiler_2026-10-24.zip',
    'ConZFC_Shared_Binomial_Certificates_2026-10-24.zip',
    'ConZFC_Shared_Pell_Bound_261_2026-10-24.zip',
    'ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip',
    'ConZFC_Weak_Carriers_and_Shared_Signs_2026-10-24.zip',
]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def archive_bytes(relative):
    path = REPO / relative
    return path.read_bytes() if path.exists() else subprocess.check_output(
        ['git', 'show', COMMIT + ':' + relative], cwd=REPO)


def collect():
    archives = []
    for name in NAMES:
        relative = 'docs/incoming/' + name
        blob = archive_bytes(relative)
        members = []
        with zipfile.ZipFile(BytesIO(blob)) as archive:
            seen = set()
            for info in archive.infolist():
                if info.is_dir():
                    continue
                path = PurePosixPath(info.filename)
                need(not path.is_absolute() and '..' not in path.parts, 'unambiguous archive member')
                need(info.filename not in seen, 'duplicate member name')
                seen.add(info.filename)
                data = archive.read(info)
                need(len(data) == info.file_size, 'complete member length')
                members.append(dict(name=info.filename, bytes=len(data),
                                    compressed_bytes=info.compress_size, crc32=info.CRC,
                                    sha256=sha256(data).hexdigest()))
        archives.append(dict(path=relative, bytes=len(blob), sha256=sha256(blob).hexdigest(),
                             members=members, member_count=len(members),
                             uncompressed_bytes=sum(m['bytes'] for m in members)))
    return dict(schema='inert_zip_inventory_v1', commit=COMMIT,
                incoming_programs_executed=False, archives=archives)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=Path, default=HERE / 'INVENTORY.json')
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    actual = collect()
    text = json.dumps(actual, indent=2, sort_keys=True) + '\n'
    need(args.inventory.read_text() == text, 'every archive/member pin reproduces exactly')
    receipt = dict(status='PASS', optimized_python=bool(sys.flags.optimize),
                   immutable_commit=COMMIT, archives=len(actual['archives']),
                   members=sum(a['member_count'] for a in actual['archives']),
                   inventory_sha256=sha256(args.inventory.read_bytes()).hexdigest(),
                   reader_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   archive_code_imported_or_executed=False, archives_extracted_or_restored=False)
    output = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.receipt.exists():
        need(args.receipt.read_text() == output, 'refuse changed receipt overwrite')
    else:
        args.receipt.write_text(output)
    print(json.dumps(dict(status='PASS', archives=receipt['archives'], members=receipt['members'],
                          optimized_python=bool(sys.flags.optimize)), sort_keys=True))


if __name__ == '__main__':
    main()
