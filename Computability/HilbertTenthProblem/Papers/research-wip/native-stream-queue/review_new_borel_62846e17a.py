#!/usr/bin/env python3
"""New read-only archive authentication and bounded height-model checks.

No supplied program, build, imported predecessor or finite-jet suite is run.
The finite model below only corroborates the new review-side height convention.
"""
import argparse
from fractions import Fraction
import hashlib
import io
import json
import math
from pathlib import Path
import re
import subprocess
import zipfile

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT = '62846e17a78ee588f0d3686c966c1cde9a0f1bb9'
ARCHIVE = 'docs/incoming/Borel_Conjugacy_Divisibility_Threshold.zip'
ARCHIVE_SHA = 'affb3707e92ac55290e204d2adc786ac126b0da9bb878d0c754f138084a26b8d'
PREFIX = 'borel_conjugacy/'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/'
COVERAGE = {
    'borel_conjugacy.tex': (1874, 'complete mathematical text read and challenged; external references not independently reviewed'),
    'README.md': (101, 'complete delivery guide read'),
    'verify_jets.py': (284, 'complete inert source read; no execution or import'),
    'verification_report.json': (127, 'complete saved record read as data; no run replay'),
    'MANIFEST.sha256': (5, 'complete checksum manifest verified'),
}


def check(ok, reason):
    if not ok:
        raise ValueError(reason)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def span(raw, start, end):
    lines = raw.splitlines(keepends=True)
    check(1 <= start <= end <= len(lines), 'read span bounds')
    return {'start_line': start, 'end_line': end,
            'raw_span_sha256': sha(b''.join(lines[start-1:end]))}


def prime_factors(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def finite_height_checks():
    # Known finite halting times (>=1) plus an explicit never-halting toy state.
    # This is not a decision procedure for nonhalting in the review theorem.
    times = {2: 1, 3: 4, 5: None, 7: 2, 11: 6}
    def member(x):
        for p, exponent in prime_factors(x.denominator).items():
            halt_time = times.get(p, 1)
            if halt_time is not None and halt_time <= exponent:
                return False
        return True
    accepted = sorted({Fraction(a, b) for a in range(-12, 13)
                       for b in range(1, 61) if member(Fraction(a, b))})
    closure = 0
    for x in accepted:
        for y in accepted:
            check(member(x+y) and member(x-y), 'height-bounded subgroup closure')
            closure += 2
    thresholds = []
    for p, halt_time in times.items():
        for j in range(0, 9):
            got = member(Fraction(1, p**j))
            expected = j == 0 or halt_time is None or j < halt_time
            check(got == expected, 'one-step height convention')
            thresholds.append([p, halt_time, j, got])
        if halt_time is not None:
            witness = Fraction(1, p**(halt_time-1))
            check(member(witness) and not member(witness/p), 'finite-height unit obstruction')
        else:
            for x in accepted:
                check(member(p*x) and member(x/p), 'infinite-height toy unit')
    return {'fixed_toy_halting_times': {str(p): t for p, t in times.items()},
            'accepted_test_rationals': len(accepted), 'closure_checks': closure,
            'threshold_checks': thresholds,
            'scope': 'finite corroboration only; no claim to decide real machine nonhalting'}


def build():
    raw = git('show', COMMIT+':'+ARCHIVE)
    check(sha(raw) == ARCHIVE_SHA, 'immutable archive pin')
    z = zipfile.ZipFile(io.BytesIO(raw))
    names = z.namelist()
    check(len(names) == len(set(names)) == 6, 'unique six-member inventory')
    files = {name: z.read(name) for name in names}
    rows = []
    for info in z.infolist():
        check(not info.is_dir(), 'regular member expected')
        data = files[info.filename]
        base = info.filename.removeprefix(PREFIX)
        row = {'path': info.filename, 'bytes': len(data), 'sha256': sha(data),
               'compressed_bytes': info.compress_size, 'crc32': f'{info.CRC:08x}'}
        if base in COVERAGE:
            expected_lines, detail = COVERAGE[base]
            check(len(data.splitlines()) == expected_lines, 'member line count')
            row['coverage'] = {'kind': 'complete_text_read', 'detail': detail,
                               'spans': [span(data, 1, expected_lines)]}
        else:
            check(base == 'borel_conjugacy.pdf', 'unexpected member')
            row['coverage'] = {'kind': 'bytes_only',
                               'detail': 'no rendering, build or page-count verification'}
        rows.append(row)
    manifest_entries = []
    for line in files[PREFIX+'MANIFEST.sha256'].decode().splitlines():
        expected, name = line.split(None, 1)
        check(sha(files[PREFIX+name]) == expected, 'manifest '+name)
        manifest_entries.append(name)
    check(len(manifest_entries) == 5, 'manifest coverage')
    tex = files[PREFIX+'borel_conjugacy.tex'].decode()
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
    check(len(labels) == len(set(labels)), 'duplicate source label')
    unresolved = sorted(set(refs)-set(labels))
    check(not unresolved, 'unresolved simple references')
    recorded = json.loads(files[PREFIX+'verification_report.json'])
    check(sum(recorded['checks'].values()) == recorded['total_checks'] == 143, 'saved count arithmetic')
    context = []
    specs = [
        ('docs/incoming/README.md', [(1,129),(220,345),(410,438)]),
        ('Algebra/SurrealNumbers/AGENTS.md', [(1,182)]),
        (HOST+'README.md', [(18,60)]),
        (HOST+'article.tex', [(36434,36476)]),
    ]
    for name, spans in specs:
        data = git('show', COMMIT+':'+name)
        context.append({'commit': COMMIT, 'path': name,
                        'blob': git('rev-parse', COMMIT+':'+name).decode().strip(),
                        'bytes': len(data), 'sha256': sha(data),
                        'read_spans': [span(data, a, b) for a, b in spans]})
    return {'collector_sha256': sha(Path(__file__).read_bytes()),
            'archive': {'commit': COMMIT, 'path': ARCHIVE,
                        'blob': git('rev-parse', COMMIT+':'+ARCHIVE).decode().strip(),
                        'bytes': len(raw), 'sha256': sha(raw), 'members': rows},
            'manifest': {'verified_entries': manifest_entries},
            'source_labels': {'labels': len(labels), 'simple_reference_occurrences': len(refs),
                              'unresolved': unresolved},
            'saved_record': {'status': recorded['status'], 'total_checks': 143,
                             'replayed': False},
            'repository_context': context,
            'new_review_height_lemma_checks': finite_height_checks(),
            'scope': {'supplied_or_predecessor_programs_executed': False,
                      'PDF_built_or_rendered': False, 'external_sources_reviewed': False,
                      'repo_mutated': False,
                      'new_computability_lemma': 'decidable Gamma membership can have co-c.e.-complete Euler conjugacy',
                      'paid_integer_compiler_supplied': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    raw = (json.dumps(build(), sort_keys=True, indent=2)+'\n').encode()
    if args.output:
        with args.output.open('xb') as handle:
            handle.write(raw)
    else:
        check(args.expect.read_bytes() == raw, 'receipt mismatch')
    print('PASS: six-member metadata, five manifest entries, and bounded height-model checks; no report code run')


if __name__ == '__main__':
    main()
