#!/usr/bin/env python3
"""Pinned, bounded synthesis audit. No original suites or repository mutations."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

COMMITS = ('d51fafea806cbd48ba29be017eff85cdd9653b14', '0be9b913487fa2cc0e16cea6545c55f33b4446d8')
BASE = 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/'
PATHS = (BASE+'article.tex', BASE+'README.md', 'Algebra/SurrealNumbers/docs/NOTATION.md', 'Algebra/SurrealNumbers/AGENTS.md')
# One immutable SHA per file and publication; git blob IDs are also recorded.
SHAS = (
 ('8e40fe735efd3dfe3dc0b24a6c7cafb642203f43b7e8dc303804633fe7b99611',
  'f0b5a8dd762e56fbf58b4bdeeea3eb5be1904926a396c1d2206a9d0ea21e8fd7',
  'e183d8bab432005a3a517848935b9c5251e6a18cc3c3cabd068959ffa69aa7e6',
  'ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039'),
 ('728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503',
  '8fc8b16c54a45cab946f383ee47b9f87b31b105939e0d65f681c88a1f1a6a568',
  '1c6b246bfe5889177a7c9557b9c6d64d3654bfb099a12508ef3904a6c9f052e9',
  'ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039'))


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], check=True, capture_output=True, timeout=60).stdout


def equal_typed(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(equal_typed(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(equal_typed(x, y) for x, y in zip(a, b))
    return a == b


def counterexample():
    # Exact finite first successor stages of the published W-pullback recursion.
    empty = frozenset()
    ranks = {0: {(): 0}, 1: {('-',): 0, ('+',): 1},
             2: {('+','-'): 0, ('-','-'): 1, ('+','+'): 2, ('-','+'): 3}}
    stages = [()]
    for _ in range(3):
        previous = stages[-1]
        subsets = [frozenset(previous[i] for i in range(len(previous)) if mask & (1 << i))
                   for mask in range(1 << len(previous))]
        code = lambda a: tuple('+' if x in a else '-' for x in previous)
        ordered = tuple(sorted(subsets, key=lambda a: ranks[len(previous)][code(a)]))
        stages.append(ordered)
    singleton = frozenset((empty,))
    require(stages[2] == (empty, singleton), 'w2 orientation')
    restricted = tuple(x for x in stages[3] if x in stages[2])
    require(restricted == (singleton, empty), 'w3 must reverse w2 on V2')
    return {'W_length1': ['-', '+'], 'W_length2': ['+-', '--', '++', '-+'],
            'w2': ['empty', '{empty}'], 'w3_restricted_to_V2': ['{empty}', 'empty'],
            'successor_stages_constructed': 3,
            'conclusion': 'uniformly defined does not imply compatible under restriction'}


def code_convention_checks():
    count = 0
    # Every permutation on {0,...,n-1}, including presentations with trailing
    # fixed points; normalization first removes those trailing fixed points.
    for n in range(7):
        for p in itertools.permutations(range(n)):
            support = tuple(i for i, x in enumerate(p) if i != x)
            require(set(p[i] for i in support) == set(support), 'support invariant')
            lam = max(support, default=-1) + 1
            normalized = p[:lam]
            support_map = {i: p[i] for i in support}
            restored = tuple(support_map.get(i, i) for i in range(lam))
            require(restored == normalized, 'normalized -> support -> normalized')
            require({i: restored[i] for i in range(lam) if restored[i] != i} == support_map,
                    'support -> normalized -> support')
            require(all(support_map.get(i, i) == (normalized[i] if i < lam else i)
                        for i in range(n+2)), 'evaluation equality')
            count += 1
    return count


def run(repo, patch):
    snapshot = {}
    pins = []
    for ci, commit in enumerate(COMMITS):
        for pi, path in enumerate(PATHS):
            data = git(repo, 'show', commit+':'+path)
            require(sha(data) == SHAS[ci][pi], 'publication pin: '+path)
            pins.append({'commit': commit, 'path': path, 'sha256': sha(data),
                         'blob': git(repo, 'rev-parse', commit+':'+path).decode().strip()})
            snapshot[(commit,path)] = data
    article = snapshot[(COMMITS[-1],PATHS[0])].decode()
    lines = article.splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith('% ---- ')]
    hand = []
    for n, i in enumerate(starts):
        j = starts[n+1] if n+1 < len(starts) else len(lines)
        if lines[i].startswith('% ---- hand chunk'):
            hand.append({'name': lines[i].split('hand chunk ',1)[1], 'first_line': i+1,
                         'last_line': j, 'sha256': sha(('\n'.join(lines[i:j])+'\n').encode())})
    require(len(hand) == 98, 'new editorial chunk census')
    require(article.count('produces a coherent sequence of well-orders') == 1, 'first finding source')
    require(article.count('precisely a coherent well-ordering of the power sets') == 1, 'second finding source')
    patchdata = Path(patch).read_bytes()
    require(sha(patchdata) == '0004ce2f78d1ebd1f5986948077ca1a70488a1793bb4b9bf67cc088f639aa839', 'exact three-change patch pin')
    with tempfile.TemporaryDirectory(prefix='surreal-synthesis-') as tmp:
        target = Path(tmp)
        for path in PATHS[:2]:
            p = target/path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(snapshot[(COMMITS[-1],path)])
        cmd = ['patch', '--batch', '--fuzz=0', '-p1', '-i', str(Path(patch).resolve())]
        subprocess.run(cmd+['--dry-run'], cwd=target, check=True, capture_output=True, timeout=30)
        subprocess.run(cmd, cwd=target, check=True, capture_output=True, timeout=30)
        patched = []
        for path in PATHS[:2]:
            data = (target/path).read_bytes()
            expected = snapshot[(COMMITS[-1],path)]
            expected = expected.replace(b'produces a coherent sequence of well-orders',b'produces a uniformly defined sequence of well-orders')
            expected = expected.replace(b'precisely a coherent well-ordering of the power sets',b'precisely a uniform well-ordering of the power sets')
            expected = expected.replace(b'the largest delivered file is',b'the largest delivered non-PDF file is')
            require(data == expected, 'patch exceeds three exact prose corrections')
            patched.append({'path':path,'sha256':sha(data)})
    return {'schema':1, 'scope':'new mathematical synthesis only; not a transfinite proof certificate',
            'pins':pins,'new_editorial_chunks':hand,'new_editorial_lines':sum(x['last_line']-x['first_line']+1 for x in hand),
            'choice_coherence_counterexample':counterexample(),
            'finite_code_convention_roundtrips':code_convention_checks(),
            'findings':[{'priority':'P3','kind':'unsupported restriction coherence','article_lines':[3640,7336]},
                        {'priority':'P3','kind':'largest delivered file qualifier','README_line':82,
                         'largest_non_PDF_bytes':126780,'largest_delivered_bytes':543575,
                         'inventory_evidence':'independent four-archive preservation census by sibling reviewer'}],
            'patch_sha256':sha(patchdata),'patched_files':patched,
            'original_author_suites_rerun':False,'Lean_or_PDF_checks':False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--patch', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--expect', type=Path)
    ns = ap.parse_args()
    result = run(ns.repo, ns.patch)
    if ns.expect:
        require(equal_typed(result, json.loads(ns.expect.read_text())), 'saved receipt mismatch')
    ns.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS', 'editorial_chunks':len(result['new_editorial_chunks']),
                      'finite_code_convention_roundtrips':result['finite_code_convention_roundtrips'],
                      'findings':len(result['findings'])},sort_keys=True))


if __name__ == '__main__':
    main()
