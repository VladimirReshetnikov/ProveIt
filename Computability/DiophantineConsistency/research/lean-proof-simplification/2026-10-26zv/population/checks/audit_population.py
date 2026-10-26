#!/usr/bin/env python3
"""Read-only, portable stdlib audit. Not a Lean elaborator or proof checker.

Usage: python3 population/checks/audit_population.py
       python3 population/checks/audit_population.py --upstream /path/to/pinned/repo
Reads delivered files, checks exact body-only replacements and patch replay,
then exhausts bounded arithmetic models. Writes JSON to stdout only.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import itertools
import json
import re


def require(condition, message="audit condition failed"):
    if not condition:
        raise AssertionError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def replay_patch(before, patch):
    old = before.splitlines(keepends=True)
    lines = patch.splitlines(keepends=True)
    require(lines[0].startswith('--- a/') and lines[1].startswith('+++ b/'))
    out, cursor, j = [], 0, 2
    while j < len(lines):
        m = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@\n', lines[j])
        require(m, (j, lines[j]))
        start, old_count, _, new_count = (int(x) if x else 1 for x in m.groups())
        at = start - 1
        require(cursor <= at)
        out.extend(old[cursor:at])
        cursor, seen_old, seen_new = at, 0, 0
        j += 1
        while j < len(lines) and not lines[j].startswith('@@'):
            line = lines[j]
            require(line[:1] in (' ', '+', '-'))
            if line[:1] in (' ', '-'):
                require(cursor < len(old) and old[cursor] == line[1:])
                cursor += 1
                seen_old += 1
            if line[:1] in (' ', '+'):
                out.append(line[1:])
                seen_new += 1
            j += 1
        require((seen_old, seen_new) == (old_count, new_count))
    out.extend(old[cursor:])
    return ''.join(out)


def check_artifacts(root, upstream):
    manifest = json.loads((root / 'evidence/accounting.json').read_text())
    require(manifest['production_helpers_added'] == 0)
    require(manifest['production_imports_added'] == 0)
    results = []
    for c in manifest['changes']:
        src = (root / 'source' / c['file']).read_bytes()
        dst = (root / 'candidates' / c['file']).read_bytes()
        patch = (root / 'patches' / c['patch']).read_bytes()
        require(digest(src) == c['source_sha256'])
        require(digest(dst) == c['candidate_sha256'])
        require(digest(patch) == c['patch_sha256'])
        old, new, p = src.decode(), dst.decode(), patch.decode()
        require(old.count(c['before']) == 1)
        require(new == old.replace(c['before'], c['after'], 1))
        require(replay_patch(old, p) == new)
        expected_patch = ''.join(difflib.unified_diff(
            old.splitlines(True), new.splitlines(True),
            fromfile='a/' + c['repository_path'], tofile='b/' + c['repository_path']))
        require(p == expected_patch)
        require(len(old.splitlines()) == c['whole_file_physical_before'])
        require(len(new.splitlines()) == c['whole_file_physical_after'])
        require(len(old.splitlines()) - len(new.splitlines()) == c['net_physical_deleted'])
        if upstream:
            require((upstream / c['repository_path']).read_bytes() == src)
        results.append({k: c[k] for k in (
            'file', 'theorem', 'whole_file_physical_before',
            'whole_file_physical_after', 'net_physical_deleted', 'classification')})
    require(sum(c['net_physical_deleted'] for c in manifest['changes']) == 7)
    # The exact-replacement check above proves all material outside the two
    # changed proof spans is byte-identical, including headers and omit scopes.
    return {'pin': manifest['pin'], 'body_only_replacements': results,
            'upstream_bytes_checked': upstream is not None,
            'new_helpers': 0, 'new_imports': 0, 'net_physical_deleted': 7}


def population(u, a, f, m, h):
    q = 1 << u
    packed = (a + m) + q * (f + h) + q*q * max(q-1-a, 0) + q**3 * max(q-1-f, 0)
    return packed.bit_count()


def four_blocks(q, c, f, mc, mf, j):
    return (max(c-1, 0) + (mc*j+1) + q*(f+max(mf*j-1, 0))
            + q*q*max(q-c, 0) + q**3*max(q-f-1, 0))


def rank(q, c, f, mc, mf, beta, j):
    return (q*(q-f)-c)*(q*q-1) + (mc+q*(mf+beta))*j


def finite_models():
    counts = dict(disjoint_sum=0, exact_population=0, calibrated_population=0,
                  unrestricted_top_block=0, cube_growth=0, packing_cast_and_strict_rank=0)
    for u in range(8):
        q = 1 << u
        for a, m in itertools.product(range(q), repeat=2):
            if a & m == 0:
                require(a + m == (a | m) and a + m < q)
                counts['disjoint_sum'] += 1
    for u in range(6):
        q = 1 << u
        pairs = [(a, m) for a, m in itertools.product(range(q), repeat=2) if a & m == 0]
        for (a, m), (f, h) in itertools.product(pairs, repeat=2):
            actual = population(u, a, f, m, h)
            require(actual == 2*u + m.bit_count() + h.bit_count())
            counts['exact_population'] += 1
            if m.bit_count() + h.bit_count() == u+2:
                require(actual == 3*u+2)
                counts['calibrated_population'] += 1
    for u in range(4):
        q = 1 << u
        for a, b, c in itertools.product(range(q), repeat=3):
            for d in (0, 1, q, q*q+3):
                require((a+q*b+q*q*c+q**3*d).bit_count() == sum(x.bit_count() for x in (a,b,c,d)))
                counts['unrestricted_top_block'] += 1
    for u in range(257):
        require(2*u <= 3*u < 2**(3*u) == (2**u)**3)
        counts['cube_growth'] += 1
    for u in range(6):
        q = 1 << u
        # Empty C,F domain at u=0 is preserved, not silently replaced by a
        # nonexistent positive C. Small models are not literal 94517-bit q.
        for c in range(1, q):
            for f in range(q-c):
                for j in range(1, q):
                    if (q-1) % j:
                        continue
                    beta = (q-1)//j
                    for mc in range(3):
                        for mf in range(1, 4):
                            packed = four_blocks(q, c, f, mc, mf, j)
                            actual_rank = rank(q, c, f, mc, mf, beta, j)
                            require(packed == actual_rank and q**3 <= packed)
                            require(2*u < actual_rank)
                            counts['packing_cast_and_strict_rank'] += 1
    # Mutation witnesses: these are expected failures of weakened contracts,
    # not counterexamples to the delivered Lean statements.
    require(not (1+1 < (1 << 1)))  # omit disjointness
    require(population(1, 1, 0, 1, 0) != 2*1 + (1).bit_count())  # exact, not ≤
    require((2+2*1).bit_count() != (2).bit_count()+(1).bit_count())  # omit low block bound
    require(four_blocks(2, 0, 1, 0, 1, 1) != rank(2, 0, 1, 0, 1, 1, 1))  # omit C>0
    require(not (2*1 < rank(2, 2, 2, 0, 1, 1, 1)))  # omit C+F<q
    q,c,f,mc,mf,beta,j = 2,1,0,0,1,1,1
    require(four_blocks(q,c,f,mc,mf,j) != rank(q,c,f,mc,mf+beta,beta,j))  # shift twice
    return {'counts': counts, 'weakened_contract_mutations_rejected': 6,
            'literal_current_constants_evaluated': False,
            'scope': 'Bounded independent arithmetic models; not Lean acceptance or a universal proof.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--upstream', type=Path)
    args = parser.parse_args()
    report = {'status': 'PASS', 'artifacts': check_artifacts(args.root, args.upstream),
              'finite_models': finite_models(),
              'lean': 'UNCOMPILED; no elaboration, kernel check, axiom audit, or performance benchmark.'}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
