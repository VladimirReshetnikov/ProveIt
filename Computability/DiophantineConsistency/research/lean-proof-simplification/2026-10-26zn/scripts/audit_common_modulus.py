#!/usr/bin/env python3
"""Audit the exact literal-data fixture, common certificate, and current old tables.

Run with --repository pointing to the reviewed ProveIt checkout. This is a
reproducibility/data audit, not a substitute for Lean kernel checking.
"""
import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

EXPECTED_COMMIT = 'e1c8914bc7064d9a8e7c06171a18069a949badd0'
BASE_SHA256 = '6e6812f7181a4b7fa5c558aef5f369c3068c21870710d522a979c39c877c8f4f'
DATA_SHA256 = '38a11d1ef8d3391074d4cd347e0f764417c6502afd9a6a064d54266456396f5b'
REL = 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
M = 47 * 2011 * 120199
PRIMES = (47, 2011, 120199)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def chunks(text):
    pattern = r'def chunk(\d+) : List \(ℕ × ℕ\) := \[(.*?)\]'
    result = {}
    for name, body in re.findall(pattern, text, re.S):
        result[name] = [tuple(map(int, p)) for p in re.findall(r'\((\d+), (\d+)\)', body)]
    return result


def horner(rows, radix, modulus):
    value = 0
    for _, coefficient in rows:
        value = (value * radix + 2 * coefficient) % modulus
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    packet = Path(__file__).resolve().parents[1]
    root = args.repository / REL
    raw = (root / 'CurrentKernelResidues2011.lean').read_bytes()
    data_raw = (root / 'WangTiles942PhysicalData.lean').read_bytes()
    assert digest(raw) == BASE_SHA256, 'Wrong or modified proof baseline'
    assert digest(data_raw) == DATA_SHA256, 'Wrong or modified literal-data baseline'
    baseline = raw.decode()
    actual_data = data_raw.decode()
    fixture = (packet / 'lean/CommonModulusCertificate.lean').read_text()
    proposed = (packet / 'proposed' / REL / 'CurrentKernelResidues2011.lean').read_text()
    numerical = json.loads((packet / 'evidence/arithmetic/common-modulus-data.json').read_text())

    original_chunks = chunks(actual_data)
    fixture_chunks = chunks(fixture)
    assert original_chunks == fixture_chunks, 'Fixture coefficients changed'
    assert set(original_chunks) == {f'{i:02}' for i in range(59)}
    all_rows = sum((original_chunks[f'{i:02}'] for i in range(59)), [])
    assert len(all_rows) == 941
    for name, rows in original_chunks.items():
        expected_len = 13 if name == '58' else 16
        assert len(rows) == expected_len

    old_blocks = re.findall(
        r'private theorem block_(\d+)_(\d+) : evaluate \((\d+) : ZMod (\d+)\) '
        r'chunk\d+ = (\d+) :=', baseline)
    assert len(old_blocks) == 177
    for prime, name, radix, modulus, residue in old_blocks:
        assert prime == modulus
        assert horner(original_chunks[name], int(radix), int(modulus)) == int(residue)

    radix = pow(2, 47, M)
    assert numerical['M'] == M and numerical['radix'] == radix
    common_blocks = re.findall(
        r'private theorem common_(\d+) : evaluate \((\d+) : ZMod (\d+)\) '
        r'chunk\d+ = (\d+) :=', proposed)
    assert len(common_blocks) == 59
    for name, r, modulus, residue in common_blocks:
        assert (int(r), int(modulus)) == (radix, M)
        assert horner(original_chunks[name], radix, M) == int(residue)
    for block in numerical['blocks']:
        name = block['index']
        assert block['length'] == len(original_chunks[name])
        assert block['residue'] == horner(original_chunks[name], radix, M)

    row_value = horner(all_rows, radix, M)
    controls = sum(2 * pow(2, a+j, M) * pow(radix, 1005-b-j, M)
        for a, b, n in [(10,978,8), (18,960,9), (27,969,8), (35,942,9)]
        for j in range(n)) % M
    kernel = (pow(radix,18,M) + pow(radix,1004,M) + pow(radix,2020,M)
        + 2*34876427265*pow(radix,1005,M) + row_value*pow(radix,64,M)
        + controls) % M
    assert numerical['rows'] == row_value
    assert numerical['controls'] == controls
    assert numerical['K'] == kernel
    assert [kernel % p for p in PRIMES] == [26, 1995, 114787]

    # The proof bridge and its full physical-order statement are retained verbatim.
    prefix = baseline[:baseline.index('private theorem block_47_00')]
    assert proposed.startswith(prefix)
    suffix = baseline[baseline.index('private theorem mod_of_cast'):]
    assert proposed.endswith(suffix)
    source_path = REL + '/CurrentKernelResidues2011.lean'
    expected_patch = ''.join(difflib.unified_diff(
        baseline.splitlines(True), proposed.splitlines(True),
        fromfile='a/'+source_path, tofile='b/'+source_path))
    assert expected_patch == (packet / 'patches/01-common-modulus.patch').read_text()

    result = dict(status='passed', base_commit=EXPECTED_COMMIT,
        exact_coefficient_pairs=941, exact_chunk_definitions=59,
        baseline_block_residues_validated=177, proposed_block_residues_validated=59,
        controls_validated=34, original_reflection_prefix_preserved=True,
        original_modulus_and_Hs_suffix_preserved=True,
        base_sha256=BASE_SHA256, literal_data_sha256=DATA_SHA256,
        candidate_sha256=digest(proposed.encode()),
        checked_fixture_sha256=digest(fixture.encode()),
        baseline_lines=len(baseline.splitlines()),
        candidate_lines=len(proposed.splitlines()),
        net_lines_removed=len(baseline.splitlines())-len(proposed.splitlines()),
        common_modulus=M, common_kernel_residue=kernel,
        projection_residues={str(p):kernel%p for p in PRIMES},
        scope='Exact-source/data audit; Lean status is recorded separately')
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
