#!/usr/bin/env python3
"""Check that package 172's six ports are the integers of `P138Ports.ports6`.

Usage: py -I -X utf8 -B check_ports172.py

What the JSONs pin. `integer11_degree298_ops146.json` (298/146) and
`integer11_degree300_ops144.json` (300/144), SHA-256 pinned below, do not contain the numeric
values of their six fixed integers. In both, nodes 11..16 are symbolic leaves
`["coefficient", name]` for `beta K0 MC MF cone_A cone_B`, and the field `coefficient_binding`
names `coefficients/BINDING.json`, a path relative to the package directory.

Unlike package 138, package 172 has no `RESTORED_DEPENDENCIES.json`, and its `coefficients/`
directory is not in this repository (the intake deduplicated it). The binding is still pinned:
the package's `MANIFEST_SHA256.json` records the byte count and SHA-256 of
`coefficients/BINDING.json` and of the six `coefficients/*.bin.gz` payloads. This script resolves
each pinned entry to the repository copy with the same name under `COPIES` and requires the same
byte count and SHA-256. Those are the files package 138 is bound to, so both packages have the
same six ports.

The check, link by link:

1. each JSON's SHA-256 (the pin below and the package manifest's entry), its coefficient leaves
   (names and order) and `coefficient_binding`;
2. the manifest's `coefficients/BINDING.json` and payload entries: a repository copy exists with
   the pinned SHA-256 and size;
3. every payload of `BINDING.json`: gunzip, raw SHA-256, bits, raw bytes, minimal encoding;
   plus the `recipe` strings of the two cones;
4. the Lean side, through `check_ports138.py` (loaded from the sibling directory): its verbatim
   drift guard of the Lean definitions and its Python transcription of `P138Ports.ports6`;
5. `ports6 i` equals payload `i` (in the JSON's coefficient order) as integers;
6. mutation controls.

This is finite external evidence for the binding, not a Lean theorem.
"""
from pathlib import Path
import gzip, hashlib, importlib.util, json, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
PKG = (DC / 'con-zfc-diophantine-forms/172-pooled-powers-round21/part2'
       / 'ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/integer11')
COPIES = DC / 'candidates/constructive-integer14-quadratic/coefficients'
JSONS = [
    ('integer11_degree298_ops146.json',
     'b03239019cd6d6be7226635627e6d3ec7b03639d132f62fa8254750b2192b5e2'),
    ('integer11_degree300_ops144.json',
     'd71707fd2cee0d2119da6cda150b4d143f9fe95aafb1501f1c406421b15d22be'),
]
MANIFEST_SHA256 = '2ff2845f86e7c14000daaa447de6f2a71856ad566c36eb14c73e489b1efa05bb'

spec = importlib.util.spec_from_file_location(
    'check_ports138', DC / 'research/p138-integer11/tools/check_ports138.py')
p138 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p138)
need, PORTS, FAIL = p138.need, p138.PORTS, p138.FAIL


def main():
    print('1. the pinned JSONs')
    mdata = (PKG / 'MANIFEST_SHA256.json').read_bytes()
    need(hashlib.sha256(mdata).hexdigest() == MANIFEST_SHA256,
         f'MANIFEST_SHA256.json SHA-256 = {MANIFEST_SHA256}')
    manifest = {e['path']: e for e in json.loads(mdata)['files']}
    for name, sha in JSONS:
        data = (PKG / name).read_bytes()
        need(hashlib.sha256(data).hexdigest() == sha, f'{name} SHA-256 = {sha}')
        pin = manifest.get(name)
        need(pin is not None and pin['sha256'] == sha and pin['bytes'] == len(data),
             '  the package manifest pins the same SHA-256 and size')
        p = json.loads(data)
        leaves = [(i, r[1]) for i, r in enumerate(p['nodes']) if r[0] == 'coefficient']
        need([n for _, n in leaves] == PORTS, f'  coefficient leaves, in order: {[n for _, n in leaves]}')
        need([i for i, _ in leaves] == list(range(11, 17)), '  coefficient leaves are nodes 11..16')
        need(not any(r[0] == 'coefficient' and isinstance(r[1], int) for r in p['nodes']),
             '  the JSON carries no numeric value for any coefficient (symbolic leaves only)')
        need(p.get('coefficient_binding') == 'coefficients/BINDING.json',
             f"  coefficient_binding = {p.get('coefficient_binding')!r}")

    print('2. the manifest pins of coefficients/, resolved to repository copies')
    keys = ['coefficients/BINDING.json'] + [f'coefficients/{n}.bin.gz' for n in PORTS]
    copies = {}
    for key in keys:
        pin = manifest.get(key)
        if not need(pin is not None, f'the package manifest pins {key}'):
            continue
        need(not (PKG / key).exists(), f'  {key} is not shipped in the package directory')
        f = COPIES / Path(key).name
        b = f.read_bytes() if f.exists() else b''
        need(f.exists() and len(b) == pin['bytes'] and hashlib.sha256(b).hexdigest() == pin['sha256'],
             f"  {key} -> {f.relative_to(DC).as_posix()} ({pin['bytes']} bytes, sha256 {pin['sha256'][:16]}...)")
        copies[key] = f
    if len(copies) != len(keys):
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
