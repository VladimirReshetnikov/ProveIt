#!/usr/bin/env python3
"""Bounded independent intake of Reports 26--28; archive Python is never run."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from zipfile import ZipFile

ARCHIVES = {'Two_Parallel_Conservative_Involutions_Package.zip': '20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4', 'Sparse_Parallel_Particle_Evaluation_Package.zip': '05c1cc14cc6005540e3de9749e0d8c0d5ab0f9225f80b0852a6149674d211df3', 'Canonical_Parallel_Quartic_Certificates_Package.zip': 'bc78252b9d0e0a7d122be2c9adccfef8c0a810e20cbd06606a709a78846dc5de'}
MEMBERS = {'Two_Parallel_Conservative_Involutions_Package.zip': {'parallel-involution-report26/scientific/PROOF.md': 'fe809adaa74418bcddafc61cc5ff70102724256c310ae53fd396c2fe34ef65c9'}, 'Sparse_Parallel_Particle_Evaluation_Package.zip': {'sparse-parallel-release-20261003/scientific/PROOF.md': '28d5bdf44273790591f0043454c0f71644afbfec880eb980eee429e70fb4ae1c'}, 'Canonical_Parallel_Quartic_Certificates_Package.zip': {'parallel-quartic-release-20261003/research/PROOF.md': 'f10aea96e218475e2ceab30c5fff2a9454fb6e13295662ca18ff842a87f35636', 'parallel-quartic-release-20261003/research/example-pair-sos.json': '96715e468c3af4b489a1ce881ea0c09cdae7bffa0efca762d8e5a308c2ddbae0', 'parallel-quartic-release-20261003/research/example-pair-quartic.json': 'ddd6973f1285d60c2ae663b6b47cd933827e9e86c332cb69148c1ef45c27dca1', 'parallel-quartic-release-20261003/research/example-pair-witness.json': 'ef49bb8c56731827374123e215c608dd0d1468c8ee5fe234c2dd32524d0c2095'}}

def need(ok, why):
    if not ok:
        raise ValueError(why)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def same(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b

def read_pinned(root):
    blobs = {}
    for archive, pin in ARCHIVES.items():
        path = root / 'docs/incoming' / archive
        need(sha(path.read_bytes()) == pin, 'archive pin: ' + archive)
        with ZipFile(path) as z:
            need(len(z.namelist()) == len(set(z.namelist())), 'unique archive members')
            for member, mpin in MEMBERS[archive].items():
                b = z.read(member)
                need(sha(b) == mpin, 'member pin: ' + member)
                blobs[member] = b
    return blobs

def periodic_lemma():
    # The report's small standalone lemma example, not its particle compiler.
    # Positions are residues mod12. b=r=1, H=4, endpoint supports {-1,0}
    # and {-1,1}; predicates see the entire three-cell write interval.
    n = 12
    def distance(a, b):
        return min((a-b) % n, (b-a) % n)
    def keys(x):
        return {u for u in range(n)
                if {(v-u) % n for v in x if distance(v,u) <= 1}
                in ({n-1,0}, {n-1,1})}
    def swap(x, u):
        return x ^ {u, (u+1) % n}
    def selected(x, prospective=True):
        raw = keys(x)
        return {u for u in raw
                if all(u == v or distance(u,v) > 4 for v in raw)
                and (not prospective or keys(swap(x,u)) == raw)}
    def apply(x, prospective=True):
        y = set(x)
        for u in selected(x, prospective):
            y = swap(y,u)
        return y
    changed = multiple = 0
    for mask in range(1 << n):
        x = {i for i in range(n) if (mask >> i) & 1}
        y = apply(x)
        need(keys(x) == keys(y), 'raw keys preserved')
        need(selected(x) == selected(y), 'all selection statuses preserved')
        need(apply(y) == x and len(y) == len(x), 'involution and mass')
        changed += y != x
        multiple += len(selected(x)) > 1
    x = {0,1,2}
    bad = apply(x, False)
    need(bad == {0,1,3} and apply(bad,False) == bad and bad != x,
         'isolation-only counterexample')
    need(apply(x) == x, 'prospectivity rejects that mutation')
    need(changed > 0 and multiple > 0, 'nonvacuous periodic fixtures')
    return dict(period=n, words=1 << n, changed_words=changed,
                multiple_selected_words=multiple,
                isolation_only_counterexample=[sorted(x), sorted(bad)],
                scope='One periodic endpoint family; not an exhaustive CA proof.')

def parse_poly(rows, variables, max_degree):
    need(type(rows) is list, 'term array')
    out = {}
    for row in rows:
        need(type(row) is list and len(row) == 2, 'coefficient/monomial pair')
        c, m = row
        need(type(c) is int and c != 0 and type(m) is list, 'integer nonzero term')
        need(len(m) <= max_degree and all(type(i) is int and 0 <= i < variables for i in m), 'monomial index/degree')
        need(m == sorted(m) and tuple(m) not in out, 'canonical distinct monomial')
        out[tuple(m)] = c
    return out

def value(poly, x):
    total = 0
    for m,c in poly.items():
        p = c
        for i in m:
            p *= x[i]
        total += p
    return total

def quartic(blobs):
    base = 'parallel-quartic-release-20261003/research/'
    sos = json.loads(blobs[base + 'example-pair-sos.json'])
    full = json.loads(blobs[base + 'example-pair-quartic.json'])
    wit = json.loads(blobs[base + 'example-pair-witness.json'])
    need(sos['format'] == 'natural-quartic-sos-v1' and full['format'] == 'sparse-integer-polynomial-v1', 'data formats')
    names = sos['variable_names']
    need(type(names) is list and all(type(x) is str for x in names) and len(names) == len(set(names)) == 1502, 'distinct variables')
    need(type(sos['input_count']) is int and sos['input_count'] == 8 and type(full['input_count']) is int and full['input_count'] == 8 and type(full['variable_count']) is int and full['variable_count'] == 1502, 'interfaces')
    need(names[:8] == ['x_0_plus','x_0_minus','x_1_plus','x_1_minus','y_0_plus','y_0_minus','y_1_plus','y_1_minus'], 'literal external order')
    rows = [parse_poly(p, 1502, 2) for p in sos['residuals']]
    polynomial = parse_poly(full['terms'], 1502, 4)
    rebuilt = Counter()
    for row in rows:
        for a,c in row.items():
            for b,d in row.items():
                rebuilt[tuple(sorted(a+b))] += c*d
    rebuilt = {m:c for m,c in rebuilt.items() if c}
    need(rebuilt == polynomial, 'complete independent SOS expansion')
    counts = dict(witnesses=len(names)-8, residuals=len(rows),
                  residual_monomials=sum(map(len,rows)),
                  ordered_sos_term_bound=sum(len(p)**2 for p in rows),
                  max_residual_degree=max(len(m) for p in rows for m in p),
                  max_coefficient_bits=max(abs(c).bit_length() for p in rows for c in p.values()),
                  residual_coefficient_bits=sum(abs(c).bit_length() for p in rows for c in p.values()),
                  residual_coefficient_l1=sum(abs(c) for p in rows for c in p.values()))
    ledger=sos['ledger']; c=ledger['circuit']
    need(all(type(c[k]) is int and c[k] == v for k,v in counts.items()), 'literal residual counts')
    need(c['A'] == 220 and c['I'] == 336 and c['G'] == 382 and c['Q'] == 8 and 2*c['A']+2*c['I']+c['G'] == counts['witnesses'] and counts['residuals'] == counts['witnesses']+c['Q'], 'displayed wire ledger')
    need(ledger['n'] == 2 and ledger['T'] == 1 and ledger['inverse'] is False, 'fixed horizon example')
    need(ledger['new_rule_radius'] == 180*8+258 == 1698 and ledger['endpoint_type_count'] == 8*1*8+29*1+2 == 95, 'different semantic resources')
    x=wit['values'];need(type(x) is list and len(x) == 1502 and all(type(v) is int and v >= 0 for v in x), 'complete natural assignment')
    need(same(wit['input'],[0,5]) and same(wit['target'],[1,6]) and x[:8] == [0,0,5,0,1,0,6,0], 'external witness binding')
    need(all(value(p,x) == 0 for p in rows) and value(polynomial,x) == 0, 'all residuals and expanded quartic vanish')
    incident={i:[] for i in range(1502)}
    for row in rows:
        for i in {i for m in row for i in m}:
            incident[i].append(row)
    mutations=0
    for i in range(8,1502):
        y=list(x);y[i]+=1
        need(any(value(p,y) != 0 for p in incident[i]), 'single witness increment rejected')
        mutations+=1
    fcounts=dict(monomials=len(polynomial),degree=max(map(len,polynomial)),
                 coefficient_bits=sum(abs(c).bit_length() for c in polynomial.values()),
                 coefficient_l1=sum(abs(c) for c in polynomial.values()),
                 max_coefficient_bits=max(abs(c).bit_length() for c in polynomial.values()))
    need(fcounts == dict(monomials=12595,degree=4,coefficient_bits=29413,coefficient_l1=6567618,max_coefficient_bits=23), 'exact expanded ledger')
    return dict(residuals=counts, expanded=fcounts, accepted_assignment=True,
                rejected_single_coordinate_increments=mutations,
                scope='Pinned sample polynomial and assignment, not a general emitter audit or finite-fold universality theorem.')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo-root',type=Path,required=True)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--expect',type=Path)
    a=ap.parse_args()
    blobs=read_pinned(a.repo_root)
    r=dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),archive_pins=ARCHIVES,
           member_pins=MEMBERS,periodic=periodic_lemma(),quartic=quartic(blobs),
           scope='New bounded independent checks only. Archive code is read as data or left untouched; no archive Python, historical test suite, or emitter is run. The proof-read scope and outstanding inherited dependencies are documented in the note.')
    if a.expect:
        need(same(r,json.loads(a.expect.read_text())), 'exact typed receipt')
    if a.output:
        a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',periodic=r['periodic'],quartic=r['quartic'])))
if __name__ == '__main__':
    main()
