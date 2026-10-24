#!/usr/bin/env python3
"""Compose free positive J with the exact two-operation auxiliary-norm saving."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
DEST = ROOT / 'candidates/free-j-polarized-positive'
ARCHIVE = REPO / 'docs/incoming/ConZFC_Congruence_Certificates_2026-10-24.zip'
ARCHIVE_SHA = 'f4119b01e56f586558f0910c6deb21b83c82dfc324f884d7d95d28500ef09e63'
PREFIX = 'con_zfc_congruence_certificates/positive/'
PARENT_SHA = '5d25f7e077cd3ac6c996ec8051113950ac7f7bf5c131dcf524b33638c1dbac95'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def build():
    need(digest(ARCHIVE.read_bytes()) == ARCHIVE_SHA, 'whole incoming archive')
    files = {}
    with zipfile.ZipFile(ARCHIVE) as archive:
        for entry in archive.infolist():
            if entry.filename.startswith(PREFIX) and not entry.is_dir():
                relative = entry.filename[len(PREFIX):]
                files['source/positive/' + relative] = archive.read(entry)
        raw = archive.read(PREFIX + 'p12_free_J.json')
    need(digest(raw) == PARENT_SHA, 'exact free-J parent member')
    parent = json.loads(raw)
    need(parent['operations'] == 98 and parent['exact_degree'] == 70, 'reviewed parent point')
    source = parent['source']
    start = next(i for i, row in enumerate(source) if row[0] == 'vn')
    stop = next(i for i, row in enumerate(source) if row[0] == 'N') + 1
    tail = [
        ['vn', '+', 'V', 'n'],
        ['vn2', '*', 'vn', 'vn'],
        ['polarV2', '*', 'V', 'V'],
        ['polarQV2', '*', 'Q', 'polarV2'],
        ['polarCy', '-', 'polarQV2', 1],
        ['polarHpart', '*', 'oneQ', 'vn2'],
        ['h', '+', 'polarHpart', 'polarCy'],
        ['polarT', '*', 'Q', 'oneQ'],
        ['polarDh', '*', 'den', 'h'],
        ['polarA', '-', 'polarDh', 'polarT'],
        ['polarA2', '*', 'polarA', 'polarA'],
        ['polarDT', '*', 'den', 'polarT'],
        ['polar4DT', '*', 4, 'polarDT'],
        ['polarCorrection', '*', 'polar4DT', 'polarCy'],
        ['N', '+', 'polarA2', 'polarCorrection'],
    ]
    need(stop-start == 17 and len(tail) == 15, 'two-gate replacement')
    child = dict(parent)
    child['name'] = 'p12_free_J_polarized_degree70'
    child['source'] = source[:start] + tail + source[stop:]
    child['operations'] = len(child['source'])
    child['operation_breakdown'] = dict(Counter(row[1] for row in child['source']))
    child['coefficient_binding'] = 'source/positive/coefficients/BINDING.json: unchanged whole compact44 tuple, MF already shifted'
    child['status'] = 'Pointwise polynomial identity with the reviewed free-J positive parent; ordinary calibration inherited; no new Lean/internal-ZFC proof.'
    child['parent_sha256'] = digest(raw)
    need(child['operations'] == 96, 'whole literal operation count')
    files['equation.json'] = encoded(child)
    cuts = dict(schema='literal_arithmetic_cut_replacement_v1', parent_member=PREFIX+'p12_free_J.json',
        parent_sha256=digest(raw), source_prefix_length=start, parent_tail_length=stop-start,
        child_tail_length=len(tail), cut_inputs=['den', 'Q', 'oneQ', 'V', 'n'],
        cut_relation='oneQ = 1-Q', preserved_outputs=['h', 'N'],
        old_tail=source[start:stop], new_tail=tail,
        identity='(d*h+Q*(1-Q))^2-d*Q*(2*(1-Q)*(n+V))^2 = (d*h-Q*(1-Q))^2+4*d*Q*(1-Q)*(Q*V^2-1)',
        h='(1-Q)*(n+V)^2+Q*V^2-1', domain='all integer d,Q,V,n')
    files['CUT_IDENTITY.json'] = encoded(cuts)
    provenance = dict(archive=str(ARCHIVE.relative_to(REPO)), archive_sha256=ARCHIVE_SHA,
        parent_member=PREFIX+'p12_free_J.json', parent_sha256=digest(raw),
        native_tuple='whole compact44; beta=2^590069-1; MF_source shifted exactly once',
        generator_sha256=digest(Path(__file__).read_bytes()),
        source_files={name:digest(value) for name,value in files.items() if name.startswith('source/')})
    files['PROVENANCE.json'] = encoded(provenance)
    files['BUILD.json'] = encoded(dict(status='PASS', variables=12, domain='strictly positive integers',
        operations=96, exact_degree=70, sha256={name:digest(value) for name,value in files.items()},
        scope='Literal 17-to-15 gate replacement. Independent symbolic identity, topology, degree and fixed-port checks are separate.'))
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files = build()
    for name, raw in files.items():
        path = DEST / name
        if args.check:
            need(path.read_bytes() == raw, 'byte-identical ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    print(json.dumps(dict(status='PASS', check=args.check, positive_variables=12, operations=96, exact_degree=70), indent=2))


if __name__ == '__main__':
    main()
