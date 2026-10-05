#!/usr/bin/env python3
"""Fresh archive authentication and bounded review-side polynomial checks.

Only read-only Git commands and standard-library arithmetic are used. No
archive program, predecessor helper or build is imported or executed.
"""
import argparse
from collections import Counter
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

COMMIT = '78528873bde92442a3187c8adfd7a42243ae36f3'
PATH = 'docs/incoming/Two_Derivations_Borel_Conjugacy.zip'
PREFIX = 'Two_Derivations_Borel_Conjugacy/'
ARCHIVE_SHA = '01ef8ae37efcb4785cee1e55d69e732b0b6ca4e056116d1d37fa37f8c3b64e1e'
EXPECTED = {
 'two_derivations.pdf': (304096, None, 'cf5fbfff807ebdd1e233687b0ba9451d5a64971d7638aebba2b589a2f2af4471'),
 'two_derivations.tex': (62607, 1347, '697651caaa92c6f0f6a77c7ca5ba68021fea62ca4cd5e1345c1c6ef90a738144'),
 'verify.py': (9428, 220, '2371108d838e614066bd56c6b01c78187c64ca1d79374c1f017d4d5e933a2bdf'),
 'verification_report.json': (69275, 2693, 'a0b251dff0044624db31b39b909a508a7df58dc8f03c0b31545a63140a9e11aa'),
 'verification_report.txt': (410, 14, 'e2c4e1fb75b7c574fa3a2e022f368f67e16b0a6f0338f41bedb7932159e5671d'),
 'README.md': (3736, 83, '17066c0ea8cdaea167397a39f685b6578c66a94e873e4acde63cd041209f3ec4'),
 'requirements.txt': (14, 1, '25f9f1fb1988b230147a1d3092d34e09c069eb7a6c6d6df46b3973b9f2d36efc'),
 'build.sh': (391, 14, '8510428f2fd298038be3d1cbb11aab0d31318e656da0471d8d7744ddf2b197cc'),
 'SOURCE_AUDIT.md': (4810, 91, '710807f87be3f3d4b9e57a37a555a239b9552e75cc5922dc5e7468d07c9dd495'),
 'SHA256SUMS': (745, 9, 'f90f8f5330e74a1fe0350fa4c0fea7b1cf018ba26630b07ddd70cd957ad8bcb7'),
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])

def span(data, a, b):
    lines = data.splitlines(keepends=True)
    need(1 <= a <= b <= len(lines), 'line span')
    return {'start_line': a, 'end_line': b,
            'sha256': digest(b''.join(lines[a-1:b])),
            'convention': 'inclusive original-byte lines, splitlines(keepends=True)'}

def polynomial_checks():
    """Independent coefficient arithmetic for the new reviewer lemma only."""
    def add(a, b, sign=1):
        out = dict(a)
        for n, c in b.items():
            out[n] = out.get(n, 0)+sign*c
        return {n: c for n, c in out.items() if c}
    def mul(a, b):
        out = {}
        for n, c in a.items():
            for m, d in b.items():
                out[n+m] = out.get(n+m, 0)+c*d
        return {n: c for n, c in out.items() if c}
    def euler(a):
        return {n: n*c for n, c in a.items() if n*c}
    records = []
    for halt_time in [None]+list(range(1, 33)):
        A = {0: 1} if halt_time is None else {0: 1, halt_time: 1}
        b = mul({1: 1}, A)
        bracket = add(mul(A, euler(b)), mul(b, euler(A)), -1)
        wanted = mul({1: 1}, mul(A, A))
        need(bracket == wanted and bracket.get(1) == 1, 'noncommuting pair formula')
        need(len(A) <= 2 and min(A) == 0 and A[0] == 1, 'support/leading certificate')
        need((A == {0: 1}) == (halt_time is None), 'toy coefficient equality')
        records.append({'finite_control_halt_time': halt_time,
                        'A': sorted(A.items()), 'bracket': sorted(bracket.items())})
    return {'cases': len(records), 'records': records,
            'scope': 'Explicit chosen polynomials and exact bracket identity only. Null denotes A=1 as a formal control; no machine is simulated and no nonhalting inference is tested.',
            'nonhalting_oracle_used': False,
            'halting_reduction_proved_by_finite_tests': False}

def make(root):
    raw = git(root, 'show', COMMIT+':'+PATH)
    need(len(raw) == 333422 and digest(raw) == ARCHIVE_SHA, 'archive pin')
    blob = git(root, 'rev-parse', COMMIT+':'+PATH).decode().strip()
    need(blob == '47a347637470f303db782f000508797b352b771f', 'archive Git blob')
    members = []
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        infos = [i for i in z.infolist() if not i.is_dir()]
        need(len(infos) == 10 and {i.filename for i in infos} ==
             {PREFIX+n for n in EXPECTED}, 'archive paths')
        contents = {i.filename: z.read(i.filename) for i in infos}
        for info in sorted(infos, key=lambda x: x.filename):
            name = info.filename[len(PREFIX):]
            data = contents[info.filename]
            size, lines, pin = EXPECTED[name]
            need(len(data) == size and digest(data) == pin, 'member pin '+name)
            entry = {'path': info.filename, 'bytes': size, 'sha256': pin,
                     'compressed_bytes': info.compress_size, 'crc32': f'{info.CRC:08x}',
                     'compression_method': info.compress_type, 'external_attributes': info.external_attr}
            if lines is None:
                entry['coverage'] = 'PDF bytes authenticated only; no read/render/build'
            else:
                need(len(data.splitlines()) == lines, 'line count '+name)
                entry['line_count'] = lines
                if name == 'verification_report.json':
                    entry['coverage'] = 'Entire saved JSON parsed inertly; only stated spans human-read'
                    entry['reads'] = [span(data, 1, 115), span(data, 2649, 2693)]
                else:
                    entry['coverage'] = 'Complete text read; supplied scripts inert'
                    entry['reads'] = [span(data, 1, lines)]
            members.append(entry)
        manifest = []
        for line in contents[PREFIX+'SHA256SUMS'].decode().splitlines():
            h, name = line.split(None, 1)
            need(digest(contents[PREFIX+name]) == h, 'internal manifest '+name)
            manifest.append(name)
        need(set(manifest) == set(EXPECTED)-{'SHA256SUMS'}, 'manifest coverage')
    tex = contents[PREFIX+'two_derivations.tex']
    labels = re.findall(rb'\\label(?:\[[^\]]*\])?\{([^}]+)\}', tex)
    refs = re.findall(rb'\\(?:[cC]ref|ref|eqref|autoref)\{([^}]+)\}', tex)
    targets = {item.strip() for group in refs for item in group.split(b',')}
    need(len(labels) == len(set(labels)) and targets <= set(labels), 'simple label census')
    saved = json.loads(contents[PREFIX+'verification_report.json'])
    counts = dict(Counter(record['category'] for record in saved['checks']))
    need(counts == saved['categories'] and len(saved['checks']) == saved['assertions_passed'] == 669,
         'saved receipt consistency')
    contexts = []
    for path, a, b in [('docs/incoming/README.md', 426, 438),
                       ('Algebra/SurrealNumbers/AGENTS.md', 1, 182)]:
        data = git(root, 'show', COMMIT+':'+path)
        contexts.append({'commit': COMMIT, 'path': path,
                         'blob': git(root, 'rev-parse', COMMIT+':'+path).decode().strip(),
                         'bytes': len(data), 'sha256': digest(data), 'reads': [span(data, a, b)]})
    source_objects = []
    for path, oid in [('Algebra/SurrealNumbers/README.md', 'a7ebc59ad60d52ac4448e12ea8d2385227e34031'),
                      ('Algebra/BakerCampbellHausdorff/README.md', 'e24d8fc8dbb4901bdaa9c588367e0b5ed2797451')]:
        data = git(root, 'cat-file', 'blob', oid)
        calculated = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        need(calculated == oid, 'cited source object')
        source_objects.append({'source_claimed_path': path, 'blob': oid,
                               'bytes': len(data), 'sha256': digest(data),
                               'coverage': 'Object authenticated only; no full content or path-at-commit claim (source supplies no commit)'})
    return {'reviewer_source_sha256': digest(Path(__file__).read_bytes()),
            'status': 'PASS: archive metadata and finite reviewer arithmetic; mathematical review in MD',
            'archive': {'commit': COMMIT, 'parent': git(root, 'rev-parse', COMMIT+'^').decode().strip(),
                        'path': PATH, 'blob': blob, 'bytes': len(raw), 'sha256': digest(raw),
                        'regular_members': members, 'verified_manifest_entries': len(manifest)},
            'source_label_census': {'labels': len(labels), 'unique_labels': len(set(labels)),
                                    'simple_reference_commands': len(refs), 'distinct_targets': len(targets),
                                    'unresolved_simple_targets': []},
            'saved_author_tests': {'reported_status': saved['status'], 'reported_assertions': 669,
                                   'categories': counts, 'replayed': False,
                                   'scope': 'Recorded list and counts checked only; no symbolic tests rerun.'},
            'instruction_reads': contexts, 'cited_repository_objects': source_objects,
            'new_reviewer_finite_checks': polynomial_checks(),
            'scope': {'archive_or_predecessor_programs_executed': False,
                      'external_literature_priority_audited': False,
                      'PDF_read_or_built': False, 'Lean_or_other_build': False,
                      'paid_integer_compiler_supplied': False,
                      'new_reviewer_nonhalting_lemma': 'Explicit machine-indexed coefficient-oracle family only; see proof and encoding qualification in MD.'}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = make(args.root)
    data = (json.dumps(result, indent=2, sort_keys=True)+'\n').encode()
    if args.output:
        with args.output.open('xb') as handle:
            handle.write(data)
    else:
        need(args.expect.read_bytes() == data, 'receipt replay differs')
    print('PASS: 10 members, 9 manifest entries, saved counts, 33 new finite controls; archive code inert.')

if __name__ == '__main__':
    main()
