#!/usr/bin/env python3
"""Check the September 2026 report consolidation, without modifying evidence.

Requires the repository history at 5804c7aff. This checks editorial integrity
and finite agreement of two implementations; it does not prove either article.
"""
from collections import Counter
import importlib.util
from pathlib import Path
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
COLLECTION = ROOT / 'SetTheory/Cardinals/docs/reports'
ORDINALS = COLLECTION / 'ordinals-and-order-types'
SNAPSHOT = '5804c7aff'
LABEL = re.compile(r'\\label(?:\[[^]]*\])?\{([^}]+)\}')
CLUSTERS = [
    ('ordinal-arithmetic/lipparini-minimal-infinitary-sum',
     'article/explicit_ordinal_sum.tex',
     'ordinal-arithmetic/lipparini-minimal-operation-formula'),
    ('transfinite-words/order-types-below-omega-squared', 'article.tex',
     'transfinite-words/finite-alphabet-transfinite-words'),
]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def old_bytes(path):
    relative = path.relative_to(ROOT).as_posix()
    return subprocess.check_output(['git', 'show', f'{SNAPSHOT}:{relative}'], cwd=ROOT)


def source_checks():
    moved_count = label_count = 0
    for destination, main, former in CLUSTERS:
        dest, old = ORDINALS / destination, ORDINALS / former
        current = (dest / main).read_text(encoding='utf-8')
        labels = LABEL.findall(current)
        repeated = [x for x, count in Counter(labels).items() if count > 1]
        require(not repeated, f'Duplicate labels: {repeated}')
        base_labels = set(LABEL.findall(old_bytes(dest / main).decode('utf-8')))
        require(base_labels <= set(labels), f'Lost destination labels: {base_labels - set(labels)}')
        refs = re.findall(r'\\(?:ref|eqref|cref|Cref|pageref)\{([^}]+)\}', current)
        missing = {x for group in refs for x in group.split(',')} - set(labels)
        require(not missing, f'Unresolved source references: {missing}')
        notes = (dest / 'MERGE_NOTES.md').read_text(encoding='utf-8')
        concordance, files = notes.split('## Byte-preserved supporting files')
        pairs = re.findall(r'^\| `([^`]+)` \| `([^`]+)` \|$', concordance, re.M)
        mapping = dict(pairs)
        incoming = set(LABEL.findall(old_bytes(old / 'article.tex').decode('utf-8')))
        require(set(mapping) == incoming, f'Incomplete incoming label concordance: {former}')
        require(set(mapping.values()) <= set(labels), f'Missing concordance targets: {former}')
        moves = re.findall(r'^\| `([^`]+)` \| `([^`]+)` \|$', files, re.M)
        for source, target in moves:
            source = source.replace('\\', '/')
            target = target.replace('\\', '/')
            require(old_bytes(old / source) == (dest / target).read_bytes(),
                    f'Changed delivered evidence: {target}')
        old_files = subprocess.check_output(
            ['git', 'ls-tree', '-r', '--name-only', SNAPSHOT, '--', old.relative_to(ROOT).as_posix()],
            cwd=ROOT, text=True).splitlines()
        retired = {'README.md', 'article.tex', 'article.pdf', 'build.py', 'build.sh'}
        expected = {str((ROOT / f).relative_to(old)).replace('\\', '/') for f in old_files}
        require(expected - retired == {s.replace('\\', '/') for s, _ in moves},
                f'Unaccounted support file in {former}')
        # Unmoved evidence of the destination must also be unchanged.
        dest_files = subprocess.check_output(
            ['git', 'ls-tree', '-r', '--name-only', SNAPSHOT, '--', dest.relative_to(ROOT).as_posix()],
            cwd=ROOT, text=True).splitlines()
        for name in dest_files:
            path = ROOT / name
            if path == dest / main or path == (dest / main).with_suffix('.pdf') or path == dest / 'README.md':
                continue
            require(path.read_bytes() == old_bytes(path), f'Changed base evidence: {name}')
        require(not (old / 'article.tex').exists() and not (old / 'article.pdf').exists(),
                f'Stale standalone manuscript: {former}')
        require('Merged into' in (old / 'README.md').read_text(encoding='utf-8'), 'Missing redirect')
        moved_count += len(moves)
        label_count += len(labels)
        print(f'PASS {destination}: {len(base_labels)} original labels, '
              f'{len(incoming)} incoming destinations, {len(moves)} byte-identical moved files')
    print(f'PASS total: {label_count} unique labels across two documents; {moved_count} moved support files')


def catalogue_checks():
    source = (COLLECTION / 'manifest.tex').read_text(encoding='utf-8')
    entries = re.findall(r'^\\entry\{[^\n]*\}\s*\{([^}]+)\}\s*\{([^}]+)\}', source, re.M)
    require(len(entries) == 111, f'Expected 111 entries, got {len(entries)}')
    require(len({d for d, _ in entries}) == 111, 'Repeated catalogue destination')
    for directory, main in entries:
        main = main.replace(r'\_', '_')
        require((COLLECTION / directory / main).is_file(), f'Missing catalogue artifact: {directory}/{main}')
    require(sum(d.startswith('ordinals-and-order-types/') for d, _ in entries) == 19,
            'Wrong ordinal report count')
    for path in [ROOT / 'README.md', ROOT / 'SetTheory/README.md',
                 ROOT / 'SetTheory/Cardinals/README.md', COLLECTION / 'README.md']:
        text = path.read_text(encoding='utf-8')
        require('113 research' not in text and 'one hundred and thirteen' not in text.lower(),
                f'Stale report count: {path}')
    print('PASS catalogue: 111 unique entries, 19 ordinal reports, all PDFs exist')


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def cross_implementation_check():
    base = ORDINALS / CLUSTERS[0][0] / 'code'
    profile = load_module('merge_profile_ordinals', base / 'ordinals.py')
    block = load_module('merge_block_ordinals', base / 'block/ordinals.py')

    def convert(value, target):
        return target(tuple((convert(e, target), c) for e, c in value.terms))

    def canonical(value):
        return tuple((canonical(e), c) for e, c in value.terms)

    w = profile.OMEGA
    powers = [profile.ZERO, w, profile.omega_power(profile.finite(2)),
              profile.omega_power(w), profile.omega_power(w + profile.ONE),
              profile.omega_power(profile.omega_power(w))]
    pool = sorted({x + profile.finite(n) for x in powers for n in range(5)} |
                  {x + y for x in powers for y in powers})
    cuts = [x for x in pool if x]
    rng = random.Random(20260929)
    for _ in range(5000):
        cut = rng.choice(cuts)
        heads = tuple(x for x in rng.choices(pool, k=rng.randrange(7)) if x >= cut)
        left = profile.Profile(cut, heads).value()
        right = block.evaluate_n(convert(cut, block.Ord), [convert(x, block.Ord) for x in heads])
        require(canonical(left) == canonical(right), f'Formula mismatch: {cut}, {heads}')
    print('PASS cross-implementation: 5000 certified-profile evaluations, seed 20260929')


if __name__ == '__main__':
    sys.dont_write_bytecode = True
    source_checks()
    catalogue_checks()
    cross_implementation_check()
