#!/usr/bin/env python3
"""Deterministically reconstruct and independently audit the 202-node source.

Run from any working directory.  The bundled parent archive supplies the exact
K215 source, U222 source, and original deterministic build_source.py.  The DP
search is not required to reproduce this candidate.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
PARENT_ZIP = HERE.parent.parent / 'inputs/U222_ConU_2026-10-28.zip'
PARENT_SHA256 = 'd23e80857214900f8e0806f03f6df752af501dd0108eb92c6ed7a49795802652'
SOURCE_SHA256 = 'bc70b28ff4628db5b9b0c9bd87f560697223e4887f2568b0ece801906713db8f'
sys.dont_write_bytecode = True


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=PARENT_ZIP)
    parser.add_argument('--output', type=Path,
                        help='Optional JSON receipt; default is standard output only.')
    args = parser.parse_args()
    archive = args.archive.resolve()
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == PARENT_SHA256,
            'The parent archive does not match the pinned input.')
    spec = importlib.util.spec_from_file_location(
        'independent_commuted_source_audit', HERE / 'check_commuted_source.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    with tempfile.TemporaryDirectory(prefix='u202-source-reproduction-') as directory:
        work = Path(directory)
        extraction = work / 'parent'
        extraction.mkdir()
        with zipfile.ZipFile(archive) as z:
            for entry in z.infolist():
                require((extraction / entry.filename).resolve().is_relative_to(extraction),
                        'Unsafe path in parent archive.')
            z.extractall(extraction)
        parent = extraction / 'u222_consistency_machine'
        rebuilt = work / 'reconstructed.sites.json'
        command = [sys.executable, '-B', str(parent / 'code/build_source.py'),
                   '--baseline', str(parent / 'inputs/k215_sites.json'),
                   '--recipe', str(HERE / 'recipe.json'),
                   '--output', str(rebuilt)]
        process = subprocess.run(command, cwd=work, check=True,
                                 capture_output=True, text=True)
        build = json.loads(process.stdout)
        require(rebuilt.read_bytes() == (HERE / 'sites.json').read_bytes(),
                'Reconstruction differs from the supplied source bytes.')
        require(hashlib.sha256(rebuilt.read_bytes()).hexdigest() == SOURCE_SHA256,
                'Reconstructed source has an unexpected digest.')
        audit = checker.check(parent / 'inputs/k215_sites.json',
                              parent / 'machine/sites.json',
                              rebuilt, HERE / 'recipe.json')
        require(json.loads(json.dumps(audit)) == json.loads((HERE / 'audit.json').read_text()),
                'Independent audit differs from its bundled receipt.')
    result = {
        'status': 'EXACT_SOURCE_RECONSTRUCTION_AND_INDEPENDENT_AUDIT_PASS',
        'parent_archive_sha256': PARENT_SHA256,
        'source_sha256': SOURCE_SHA256,
        'build': build,
        'audit_status': audit['status'],
        'metrics': audit['metrics'],
        'exact_new_primitive_instructions_checked':
            audit['exact_new_primitive_instructions_checked'],
        'retained_primitive_and_control_edges_checked':
            audit['retained_primitive_and_control_edges_checked'],
        'scope': 'Source-only supplementary result. This does not construct or certify a physical Turing-machine table and does not improve the delivered U221 state bound.'
    }
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
