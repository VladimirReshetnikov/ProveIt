#!/usr/bin/env python3
"""Check that the six ports of five equations of packages 135 and 144 are `P138Ports.ports6`.

Usage: py -I -X utf8 -B check_ports135.py

What the JSONs pin. The five JSONs (SHA-256 pinned below) do not contain the numeric values of
their six fixed integers. In each, nodes 11..16 are symbolic leaves `["coefficient", name]` for
`beta K0 MC MF cone_A cone_B`, and the field `coefficient_binding` names
`coefficients/BINDING.json`, a path relative to the `scalar/` directory of the package.

Neither package ships that directory in this repository (the intake deduplicated it). The
binding is still pinned: a manifest of each package records the byte count and SHA-256 of
`coefficients/BINDING.json` and of the six `coefficients/*.bin.gz` payloads,

  * package 135: `135-cofinal-anchors-round17/MANIFEST_SHA256.json`, keys below `scalar/`;
  * package 144: `144-shared-certificates-round18/scalar/MANIFEST_SHA256.json`.

This script resolves each pinned entry to the repository copy with the same name under `COPIES`
and requires the same byte count and SHA-256. Those are the files packages 138 and 172 are bound
to, so all four packages have the same six ports.

The check, link by link, is that of `research/p172-integer11/tools/check_ports172.py`:

1. each JSON's SHA-256 (the pin below and the package manifest's entry), its coefficient leaves
   (names and order) and `coefficient_binding`;
2. the manifest's `coefficients/BINDING.json` and payload entries: a repository copy exists with
   the pinned SHA-256 and size; the two packages pin the same seven files;
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
# (package, manifest, its SHA-256, prefix of the manifest keys of `scalar/`, scalar directory,
#  JSONs with their SHA-256)
PACKAGES = [
    (135, '135-cofinal-anchors-round17/MANIFEST_SHA256.json',
     'e4e023ac3248f133752e22bb293f9be60f3b09664ed8967d46ada29c66617be8', 'scalar/',
     '135-cofinal-anchors-round17/scalar', [
         ('free_cofactor11_none.json',
          '632f92bcabf691345329363faa704685d272636ec32c8a94685a92d06bc0df54'),
         ('free_cofactor11_simple.json',
          '31d1e1824512b20f6a73ce30e4eed5c2f6f00e156844137eab65f865190e9fc1'),
         ('free_cofactor11_sharp.json',
          'dff701474d8720a20e804cf52af7fa24d36a9293360f38868536482400b255fc'),
     ]),
    (144, '144-shared-certificates-round18/scalar/MANIFEST_SHA256.json',
     '0b98799cc5dea58631e7ae72ebdbd5573ec86cb57988f0539cf244fd71b80fff', '',
     '144-shared-certificates-round18/scalar', [
         ('free_whole_center11_c316.json',
          'c015b822e0e78a3ae81f706b62cc0a7131181effd3b273991ee4c8c1a12bc7d3'),
         ('free_whole_center11_c308.json',
          '0ae634d03f271c3667b30ce72932f17db1f1dd87b3046b3984fca25f172915f9'),
     ]),
]

spec = importlib.util.spec_from_file_location(
    'check_ports138', DC / 'research/p138-integer11/tools/check_ports138.py')
p138 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p138)
need, PORTS, FAIL = p138.need, p138.PORTS, p138.FAIL
KEYS = ['coefficients/BINDING.json'] + [f'coefficients/{n}.bin.gz' for n in PORTS]


def main():
    print('1. the pinned JSONs')
    manifests = {}
    for pkg, mpath, msha, prefix, scalar, jsons in PACKAGES:
        mdata = (FORMS / mpath).read_bytes()
        need(hashlib.sha256(mdata).hexdigest() == msha, f'package {pkg}: {mpath} SHA-256 = {msha}')
        manifest = json.loads(mdata)['files']
        manifests[pkg] = manifest
        for name, sha in jsons:
            data = (FORMS / scalar / name).read_bytes()
            need(hashlib.sha256(data).hexdigest() == sha, f'{name} SHA-256 = {sha}')
            pin = manifest.get(prefix + name)
            need(pin is not None and pin['sha256'] == sha and pin['bytes'] == len(data),
                 '  the package manifest pins the same SHA-256 and size')
            p = json.loads(data)
            leaves = [(i, r[1]) for i, r in enumerate(p['nodes']) if r[0] == 'coefficient']
            need([n for _, n in leaves] == PORTS,
                 f'  coefficient leaves, in order: {[n for _, n in leaves]}')
            need([i for i, _ in leaves] == list(range(11, 17)), '  coefficient leaves are nodes 11..16')
            need(not any(r[0] == 'coefficient' and isinstance(r[1], int) for r in p['nodes']),
                 '  the JSON carries no numeric value for any coefficient (symbolic leaves only)')
            need(p.get('coefficient_binding') == 'coefficients/BINDING.json',
                 f"  coefficient_binding = {p.get('coefficient_binding')!r}")

    print('2. the manifest pins of coefficients/, resolved to repository copies')
    copies, pins = {}, {}
    for pkg, mpath, msha, prefix, scalar, jsons in PACKAGES:
        for key in KEYS:
            pin = manifests[pkg].get(prefix + key)
            if not need(pin is not None, f'package {pkg}: the manifest pins {prefix + key}'):
                continue
            need(not (FORMS / scalar / key).exists(), f'  {key} is not shipped in the package directory')
            f = COPIES / Path(key).name
            b = f.read_bytes() if f.exists() else b''
            need(f.exists() and len(b) == pin['bytes'] and hashlib.sha256(b).hexdigest() == pin['sha256'],
                 f"  {key} -> {f.relative_to(DC).as_posix()} ({pin['bytes']} bytes, sha256 {pin['sha256'][:16]}...)")
            copies[key] = f
            pins.setdefault(key, set()).add((pin['bytes'], pin['sha256']))
    if len(copies) != len(KEYS):
        print(f'MISMATCH ({len(FAIL)} failures)')
        sys.exit(1)
    need(all(len(v) == 1 for v in pins.values()), 'the two packages pin the same seven files')

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
