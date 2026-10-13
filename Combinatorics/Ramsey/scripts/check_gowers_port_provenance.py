#!/usr/bin/env python3
"""Check the quantitative port against a local pinned openai/math checkout.

This checks source provenance and retained notices, not legal compliance or
Lean proofs. It does not download or modify either checkout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PORT = ROOT / 'lib/openai-math'


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def section_theorem_source(source, name, namespace):
    """Read one of the extract's two single-theorem namespace sections."""
    marker = f'theorem {name} '
    require(source.count(marker) == 1, f'Expected exactly one extracted theorem: {name}')
    start = source.index(marker)
    end = source.find(f'\nend {namespace}\n', start)
    require(end >= 0, f'Missing namespace boundary for extracted theorem: {name}')
    return source[start:end]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('upstream', type=Path, help='local openai/math repository root')
    args = parser.parse_args()
    manifest = json.loads((PORT / 'quantitative-port-manifest.json').read_text())
    revision = subprocess.check_output(
        ['git', '-C', str(args.upstream), 'rev-parse', 'HEAD'], text=True).strip()
    require(revision == manifest['revision'], 'Upstream checkout is not at the pinned revision')
    upstream = args.upstream / 'lean'
    original_license = subprocess.check_output(
        ['git', '-C', str(args.upstream), 'show', f'{revision}:lean/LICENSE'])
    require((PORT / 'LICENSE').read_bytes() == original_license,
            'The vendored Apache license differs from the pinned upstream license')
    provenance = (PORT / manifest['provenance_notice']).read_text()
    require(manifest['revision'] in provenance and manifest['upstream'] in provenance,
            'The provenance notice does not identify the pinned upstream source')
    modified = 0
    for entry in manifest['modules']:
        path = Path(*entry['module'].split('.')).with_suffix('.lean')
        original = (upstream / path).read_bytes()
        local = (PORT / 'lean' / path).read_bytes()
        require(hashlib.sha256(original).hexdigest() == entry['upstream_sha256'],
                f'Original-source hash mismatch: {path}')
        if local != original:
            modified += 1
            require(b'Modified for ProveIt' in local,
                    f'Missing local modification notice: {path}')
        for line in original.splitlines():
            if b'copyright' in line.lower():
                require(line.strip() in local,
                        f'Missing original copyright notice: {path}')
    lattice_path = Path('OAI/Combinatorics/Progressions/Lattices')
    original = (upstream / lattice_path / 'NativeProperAffineRecovery.lean').read_text()
    extract = (PORT / 'lean' / lattice_path / 'FreimanAffineBox.lean').read_text()
    require('Modified for ProveIt' in extract and manifest['revision'] in extract,
            'Missing pinned provenance or modification notice in the Freiman extract')
    for name in ('exists_dense_cyclic_model_of_integer_vectors',
                 'exists_bounded_affine_box_of_cyclic_model'):
        require(section_theorem_source(extract, name, 'Erdos3.FreimanModel.ProveItExtract') ==
                section_theorem_source(original, name, 'Erdos3.FreimanModel'),
                f'Freiman extract differs from its pinned statement or proof body: {name}')
    original_lattice = (upstream / lattice_path / 'NormalizedLatticeSheet.lean').read_text()
    lattice_extract = (PORT / 'lean/OAI/Compat/NormalizedLatticeBasics.lean').read_text()
    require('Modified for ProveIt' in lattice_extract and manifest['revision'] in lattice_extract,
            'Missing pinned provenance or modification notice in the lattice extract')
    namespace = 'namespace OAI\n'
    geometry_section = 'section\n\nnamespace Erdos3\n\nopen Module\n'
    start = original_lattice.index(namespace)
    end = original_lattice.index(geometry_section, start)
    require(lattice_extract[lattice_extract.index(namespace):] ==
            original_lattice[start:end] + 'end OAI\n',
            'Lattice basics extract differs from its pinned declarations or proof bodies')
    original_gaussian = (upstream / lattice_path / 'LatticeSheetHaar.lean').read_text()
    gaussian_extract = (PORT / 'lean/OAI/Compat/NormalizedLatticeGaussian.lean').read_text()
    require('Modified for ProveIt' in gaussian_extract and manifest['revision'] in gaussian_extract,
            'Missing pinned provenance or modification notice in the Gaussian extract')
    start = original_gaussian.index(namespace)
    end = original_gaussian.index(
        'section\n\nnamespace Erdos3\n\nopen MeasureTheory Module Set\n', start)
    expected_gaussian = original_gaussian[start:end].replace(
        'AddSubgroup.isClosed_of_discreteTopology', 'AddSubgroup.isClosed_of_discrete')
    require(gaussian_extract[gaussian_extract.index(namespace):] ==
            expected_gaussian + 'end OAI\n',
            'Gaussian extract differs from pinned declarations or documented port adaptation')
    for entry in manifest.get('mathlib_backports', []):
        path = Path(*entry['module'].split('.')).with_suffix('.lean')
        require(entry['copyright'] in (PORT / 'lean' / path).read_text(),
                f'Missing recorded Mathlib copyright notice: {path}')
        require((PORT / entry['license_file']).is_file(),
                f'Missing recorded Mathlib license: {entry["license_file"]}')
    print(f'{len(manifest["modules"])} pinned upstream hashes match; '
          f'{modified} adapted files have modification notices.')
    print('Both Freiman extract statements and proof bodies match the pinned originals.')
    print('Lattice basics declarations and proof bodies match the pinned original.')
    print('Gaussian extract matches pinned declarations and the documented compatibility rename.')
    print('Upstream license unchanged; pinned provenance and recorded copyright notices retained.')
    print('Separate Mathlib source hashes are recorded in the manifest, not checked by this command.')


if __name__ == '__main__':
    main()
