#!/usr/bin/env python3
"""Fresh read-only archive metadata and a symbolic three-mode check.

No delivered program is imported, executed, or reconstructed for execution.
"""
import argparse
from fractions import Fraction
import hashlib
import io
import itertools
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import zipfile

REV = 'e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9'
BASE = 'a21208b3ff14a07a4c8318dbf916d543acbef043'
READS = {
    'fabius_factor_contact/README.txt': [(1, 61)],
    'fabius_factor_contact/SOURCE_NOTES.txt': [(1, 60)],
    'fabius_factor_contact/article.tex': [(1, 12), (49, 424), (1327, 1568)],
    'fabius_factor_contact/data/document_validation.json': [(1, 52)],
    'fabius_factor_contact/MANIFEST.sha256': [(1, 14)],
    'holder_zygmund_spectra/README.txt': [(1, 149)],
    'holder_zygmund_spectra/provenance.json': [(1, 69)],
    'holder_zygmund_spectra/verification/COMPUTATIONAL_NOTES.txt': [(1, 143)],
    'holder_zygmund_spectra/verification/VALIDATION_NOTES.txt': [(1, 83)],
    'holder_zygmund_spectra/verification/PDF_QA.txt': [(1, 32)],
    'holder_zygmund_spectra/holder_zygmund_spectra.tex':
        [(101, 162), (209, 506), (573, 645), (1190, 1263), (1528, 1699)],
}


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def spans(data, ranges):
    lines = data.splitlines(keepends=True)
    answer = []
    for a, b in ranges:
        need(1 <= a <= b <= len(lines), 'invalid read span')
        part = b''.join(lines[a-1:b])
        answer.append({'first': a, 'last': b, 'bytes': len(part), 'sha256': sha(part)})
    return answer


# Independent polynomials in z,theta, with rational coefficients.
def add(*items):
    out = {}
    for item in items:
        for e, c in item.items():
            out[e] = out.get(e, Fraction(0)) + c
    return {e: c for e, c in out.items() if c}


def scale(a, c):
    return {e: v*c for e, v in a.items() if v*c}


def mul(a, b):
    out = {}
    for (i, j), c in a.items():
        for (k, l), d in b.items():
            e = (i+k, j+l)
            out[e] = out.get(e, Fraction(0)) + c*d
    return {e: c for e, c in out.items() if c}


def symbolic_core():
    one, z, theta = {(0, 0): Fraction(1)}, {(1, 0): Fraction(1)}, {(0, 1): Fraction(1)}
    coefficients = {0: one, -1: scale(theta, Fraction(-1, 2)), 1: scale(theta, Fraction(-1, 2))}
    indices = [-1, 0, 1]
    matrix = [[coefficients.get(2*k-m, {}) for m in indices] for k in indices]
    zi_minus_a = [[add(z if i == j else {}, scale(matrix[i][j], -1)) for j in range(3)] for i in range(3)]
    det = {}
    for p in itertools.permutations(range(3)):
        parity = sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
        term = one
        for i in range(3):
            term = mul(term, zi_minus_a[i][p[i]])
        det = add(det, scale(term, (-1)**parity))
    expected = mul(add(z, scale(one, -1)), mul(add(z, scale(theta, Fraction(1, 2))), add(z, scale(theta, Fraction(1, 2)))))
    need(det == expected, 'generic characteristic identity')
    left = [[add(matrix[i][j], scale(one, -1) if i == j else {}) for j in range(3)] for i in range(3)]
    right = [[add(matrix[i][j], scale(theta, Fraction(1, 2)) if i == j else {}) for j in range(3)] for i in range(3)]
    for i in range(3):
        for j in range(3):
            need(not add(*(mul(left[i][k], right[k][j]) for k in range(3))), 'generic annihilator identity')
    def serial(p):
        return [[list(e), str(c)] for e, c in sorted(p.items())]
    return {'variables': ['z', 'theta'], 'matrix': [[serial(x) for x in row] for row in matrix],
            'characteristic_polynomial': serial(det),
            'characteristic_identity': '(z-1)*(z+theta/2)^2',
            'annihilator_identity': '(A-I)*(A+theta*I/2)=0',
            'identically_zero_annihilator_entries': 9,
            'scope': 'Two exact symbolic identities, not a replay of any delivered checker or an analytic spectral proof.'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True)
    parser.add_argument('--output')
    parser.add_argument('--expect')
    args = parser.parse_args()
    def git(*words):
        return subprocess.check_output(['git', '-C', args.root, *words])
    def blob(rev, path):
        data = git('show', rev+':'+path)
        return data, git('rev-parse', rev+':'+path).decode().strip()
    archives = []
    for archive_name in ['Fabius_Finite_Factor_Contact.zip', 'holder_zygmund_spectra.zip']:
        path = 'docs/incoming/'+archive_name
        data, oid = blob(REV, path)
        zf = zipfile.ZipFile(io.BytesIO(data))
        names = zf.namelist()
        need(len(names) == len(set(names)), 'duplicate ZIP names')
        member_data, members = {}, []
        for item in zf.infolist():
            p = PurePosixPath(item.filename)
            mode = item.external_attr >> 16
            need(not p.is_absolute() and '..' not in p.parts and '\\' not in item.filename, 'unsafe archive path')
            need(not item.flag_bits & 1, 'encrypted member')
            need(not stat.S_ISLNK(mode), 'symlink member')
            need(not item.is_dir(), 'unexpected directory entry')
            content = zf.read(item)  # ZipFile verifies each member's CRC.
            member_data[item.filename] = content
            parsed_json = False
            if p.suffix == '.json':
                json.loads(content)
                parsed_json = True
            reads = spans(content, READS.get(item.filename, []))
            coverage = 'selected text spans read' if reads else 'bytes authenticated only; body unread'
            if reads and sum(s['last']-s['first']+1 for s in reads) == len(content.splitlines()):
                coverage = 'full text read'
            members.append({'path': item.filename, 'bytes': len(content), 'sha256': sha(content),
                            'crc32': f'{item.CRC:08x}', 'compressed_bytes': item.compress_size,
                            'coverage': coverage, 'json_parse_pass': parsed_json,
                            'line_count': len(content.splitlines()) if reads or parsed_json else None,
                            'read_spans': reads})
        manifest_checks = []
        for name, content in member_data.items():
            if name.endswith('/MANIFEST.sha256'):
                checked = []
                for line in content.decode().splitlines():
                    expected_sha, relative = line.split(None, 1)
                    target = str(PurePosixPath(name).parent / relative.strip())
                    need(target in member_data and sha(member_data[target]) == expected_sha, 'manifest mismatch')
                    checked.append(target)
                need(set(checked) == set(member_data)-{name}, 'manifest incomplete or extraneous')
                manifest_checks.append({'path': name, 'entries': len(checked), 'all_nonmanifest_members_covered': True})
        archives.append({'path': path, 'commit': REV, 'blob': oid, 'bytes': len(data), 'sha256': sha(data),
                         'member_count': len(members), 'total_member_bytes': sum(m['bytes'] for m in members),
                         'path_unique_safe_no_symlinks_no_encryption_crc_checks': True,
                         'members': members, 'manifests': manifest_checks})
    baseline_paths = [
        'Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Wasserstein_Contact_Orders_Uniform_Factor_Resonances/wasserstein-resonance.tex',
        'Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/spectra-and-arithmetic/Arithmetic_Convolution_Factors_Fabius_Type_Laws/article.tex',
        'Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/rvachev_up_fourier_decay/Sharp_Cr_Spectral_Disks_Rvachev_Thue_Morse/article.tex',
        'Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/rvachev_up_fourier_decay/README.md',
    ]
    baselines = []
    for path in baseline_paths:
        data, oid = blob(BASE, path)
        if path == baseline_paths[2]:
            need(oid == '45a9a8724aa42f2f6812d39bb486211438dcb09f', 'declared baseline blob')
        baselines.append({'commit': BASE, 'path': path, 'blob': oid, 'sha256': sha(data),
                          'bytes': len(data), 'coverage': 'existence and identity only; body unread in this triage'})
    instructions = []
    for path, ranges in [('Analysis/FabiusFunction/AGENTS.md', [(1, 618)]), ('docs/incoming/README.md', [(426, 439)])]:
        data, oid = blob(REV, path)
        instructions.append({'path': path, 'commit': REV, 'blob': oid, 'sha256': sha(data),
                             'bytes': len(data), 'read_spans': spans(data, ranges)})
    result = {'schema': 'bounded_archive_triage_v1', 'commit': REV,
              'parent': git('rev-parse', REV+'^').decode().strip(),
              'source_sha256': sha(Path(__file__).read_bytes()), 'archives': archives,
              'baseline_identity_checks': baselines, 'instructions': instructions,
              'fresh_symbolic_check': symbolic_core(),
              'limits': ['No delivered code imported or executed.', 'No full analytic proof audit.',
                         'No PDF rendering, compilation, placement or external citation authentication.',
                         'Saved verification results authenticated and JSON parsed, not reproduced.']}
    if args.expect:
        need(json.loads(Path(args.expect).read_bytes()) == result, 'receipt mismatch')
    if args.output:
        Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': 'PASS', 'archives': len(archives),
                      'members': sum(a['member_count'] for a in archives),
                      'manifest_entries': sum(m['entries'] for a in archives for m in a['manifests']),
                      'baselines': len(baselines), 'symbolic_annihilator_entries': 9}))


if __name__ == '__main__':
    main()
