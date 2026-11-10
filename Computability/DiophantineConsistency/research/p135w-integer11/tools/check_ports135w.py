#!/usr/bin/env python3
"""Check that the six ports of package 135's weak-scale 398/121 equation are `P138Ports.ports6`.

Usage: py -I -X utf8 -B check_ports135w.py

What the JSON pins. `scalar/weak_cofactor11_none.json` (SHA-256 pinned below) does not contain
the numeric values of its six fixed integers. Nodes 11..16 are symbolic leaves
`["coefficient", name]` for `beta K0 MC MF cone_A cone_B`, and the field `coefficient_binding`
names `coefficients/BINDING.json`, a path relative to the `scalar/` directory of the package.

The package does not ship that directory in this repository (the intake deduplicated it). The
binding is still pinned: `135-cofinal-anchors-round17/MANIFEST_SHA256.json` records, below the
prefix `scalar/`, the byte count and SHA-256 of `coefficients/BINDING.json` and of the six
`coefficients/*.bin.gz` payloads. This script resolves each pinned entry to the repository copy
with the same name under `COPIES` and requires the same byte count and SHA-256. Those are the
files packages 138, 172 and 137 are bound to, and the files the three free-scale forms of this
package are bound to (`research/p135-integer11/tools/check_ports135.py`).

The check, link by link:

1. the JSON's SHA-256 (the pin below and the package manifest's entry), its topology (145 nodes,
   121 operations: 77 mul, 24 add, 20 sub; recorded exact degree 398; eleven variables in
   order), its coefficient leaves (names and order) and `coefficient_binding`;
2. the manifest's `coefficients/BINDING.json` and payload entries: a repository copy exists with
   the pinned SHA-256 and size;
3. every payload of `BINDING.json`: gunzip, raw SHA-256, bits, raw bytes, minimal encoding;
   plus the `recipe` strings of the two cones;
4. the Lean side, through `check_ports138.py` (loaded from its directory): its verbatim drift
   guard of the Lean definitions and its Python transcription of `P138Ports.ports6`;
5. `ports6 i` equals payload `i` (in the JSON's coefficient order) as integers;
6. mutation controls.

This is finite external evidence for the binding, not a Lean theorem.
"""
from pathlib import Path
import gzip, hashlib, importlib.util, json, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
FORMS = DC / 'con-zfc-diophantine-forms'
COPIES = DC / 'candidates/constructive-integer14-quadratic/coefficients'
PKG = 135
MANIFEST = '135-cofinal-anchors-round17/MANIFEST_SHA256.json'
MANIFEST_SHA = 'e4e023ac3248f133752e22bb293f9be60f3b09664ed8967d46ada29c66617be8'
PREFIX = 'scalar/'
SCALAR = '135-cofinal-anchors-round17/scalar'
NAME = 'weak_cofactor11_none'
JSON_SHA = '79d40a8b12cf8c08864e49752d4e4652f9fbaafe2863fbe56e4c805e3fc7df7b'
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
NODES, OPS_TOTAL, COUNTS, DEGREE = 145, 121, {'mul': 77, 'add': 24, 'sub': 20}, 398

spec = importlib.util.spec_from_file_location(
    'check_ports138', DC / 'research/p138-integer11/tools/check_ports138.py')
p138 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p138)
need, PORTS, FAIL = p138.need, p138.PORTS, p138.FAIL
KEYS = ['coefficients/BINDING.json'] + [f'coefficients/{n}.bin.gz' for n in PORTS]


def main():
    print('1. the pinned JSON')
    mdata = (FORMS / MANIFEST).read_bytes()
    need(hashlib.sha256(mdata).hexdigest() == MANIFEST_SHA,
         f'package {PKG}: {MANIFEST} SHA-256 = {MANIFEST_SHA}')
    manifest = json.loads(mdata)['files']
    fname = NAME + '.json'
    data = (FORMS / SCALAR / fname).read_bytes()
    need(hashlib.sha256(data).hexdigest() == JSON_SHA, f'{fname} SHA-256 = {JSON_SHA}')
    pin = manifest.get(PREFIX + fname)
    need(pin is not None and pin['sha256'] == JSON_SHA and pin['bytes'] == len(data),
         '  the package manifest pins the same SHA-256 and size')
    p = json.loads(data)
    need(p.get('name') == NAME and p.get('domain') == 'unrestricted integers',
         f"  name = {p.get('name')!r}, domain = {p.get('domain')!r}")
    need(p.get('variables') == VARS and p.get('variable_count') == len(VARS),
         f"  variables, in order: {' '.join(p.get('variables', []))}")
    counts = {k: sum(1 for r in p['nodes'] if r[0] == k) for k in COUNTS}
    need(len(p['nodes']) == NODES and p.get('output') == NODES - 1
         and counts == COUNTS == p.get('operation_counts')
         and sum(counts.values()) == OPS_TOTAL == p.get('operations'),
         f'  {NODES} nodes, {OPS_TOTAL} operations ({counts}), output node {NODES - 1}')
    need(p.get('exact_degree') == DEGREE == p.get('syntactic_degree_bound'),
         f'  recorded exact degree {DEGREE}')
    leaves = [(i, r[1]) for i, r in enumerate(p['nodes']) if r[0] == 'coefficient']
    need([n for _, n in leaves] == PORTS,
         f'  coefficient leaves, in order: {[n for _, n in leaves]}')
    need([i for i, _ in leaves] == list(range(11, 17)), '  coefficient leaves are nodes 11..16')
    need(not any(r[0] == 'coefficient' and isinstance(r[1], int) for r in p['nodes']),
         '  the JSON carries no numeric value for any coefficient (symbolic leaves only)')
    need(p.get('coefficient_binding') == 'coefficients/BINDING.json',
         f"  coefficient_binding = {p.get('coefficient_binding')!r}")

    print('2. the manifest pins of coefficients/, resolved to repository copies')
    copies = {}
    for key in KEYS:
        pin = manifest.get(PREFIX + key)
        if not need(pin is not None, f'package {PKG}: the manifest pins {PREFIX + key}'):
            continue
        need(not (FORMS / SCALAR / key).exists(), f'  {key} is not shipped in the package directory')
        f = COPIES / Path(key).name
        b = f.read_bytes() if f.exists() else b''
        need(f.exists() and len(b) == pin['bytes'] and hashlib.sha256(b).hexdigest() == pin['sha256'],
             f"  {key} -> {f.relative_to(DC).as_posix()} ({pin['bytes']} bytes, sha256 {pin['sha256'][:16]}...)")
        copies[key] = f
    if len(copies) != len(KEYS):
        print(f'MISMATCH ({len(FAIL)} failures)')
        sys.exit(1)

    print('3. BINDING.json payloads')
    binding = json.loads(copies['coefficients/BINDING.json'].read_text(encoding='utf-8'))
    print(f"  tuple: {binding.get('tuple')!r}; MF convention: {binding.get('MF_convention')!r}")
    payloads = {}
    for name in PORTS:
        pin = binding['payloads'][name]
        key = 'coefficients/' + pin['file']
        need(key in copies, f'{name}: payload file {key} is a manifest-pinned copy')
        rawb = gzip.decompress(copies[key].read_bytes())
        v = int.from_bytes(rawb, 'little')
        ok = (hashlib.sha256(rawb).hexdigest() == pin['raw_sha256'] and v.bit_length() == pin['bits']
              and len(rawb) == pin['raw_bytes'] and p138.raw(v) == rawb)
        need(ok, f"{name}: {pin['file']} raw sha256/bits ({pin['bits']})/bytes/minimal encoding")
        payloads[name] = v
    need(binding['payloads']['cone_A'].get('recipe') == '2**1113', 'cone_A recipe string is 2**1113')
    need(binding['payloads']['cone_B'].get('recipe') == '2**666104', 'cone_B recipe string is 2**666104')

    print('4. the Lean definitions (verbatim) and their evaluation')
    for rel, snippets in p138.LEAN_TEXT.items():
        text = (p138.LEAN / rel).read_text(encoding='utf-8').replace('\r\n', '\n')
        for s in snippets:
            need(s in text, f'{rel}: {s.splitlines()[0]}')
    rows = p138.lean_rows()
    need(len(rows) == 943, f'Compact943Data rows: {len(rows)}')
    lean = p138.ports6(rows)

    print('5. Lean ports6 i = payload i')
    for i, name in enumerate(PORTS):
        v = lean[i]
        src = (f'Source34Ports.ports {i}' if i < 4 else ('coneA = 2^1113' if i == 4 else 'coneB = 2^666104'))
        need(v == payloads[name]
             and hashlib.sha256(p138.raw(v)).hexdigest() == binding['payloads'][name]['raw_sha256'],
             f'ports6 {i} ({src}, {v.bit_length()} bits) = {name} payload')

    print('6. mutation controls (each must be rejected)')
    pay = [payloads[n] for n in PORTS]
    swapped = lambda a, b: [lean[b] if i == a else lean[a] if i == b else lean[i] for i in range(6)]
    controls = {
        'MC and MF swapped': swapped(2, 3),
        'cones swapped': swapped(4, 5),
        'MF unshifted (MF_native)': [lean[i] - (lean[0] if i == 3 else 0) for i in range(6)],
        'beta off by one (2^1064921)': [lean[0] + 1] + lean[1:],
        'cone_B = 2^666103': lean[:5] + [1 << 666103],
    }
    for name, vals in controls.items():
        need(vals != pay, f'rejected: {name}')

    print('ok' if not FAIL else f'MISMATCH ({len(FAIL)} failures)')
    sys.exit(0 if not FAIL else 1)


if __name__ == '__main__':
    main()
