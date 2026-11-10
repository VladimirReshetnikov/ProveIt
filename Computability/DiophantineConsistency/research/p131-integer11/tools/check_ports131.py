#!/usr/bin/env python3
"""Check that the six ports of package 131's two-root 810/112 equation are `P138Ports.ports6`.

Usage: py -I -X utf8 -B check_ports131.py

What the JSON pins. `scalar/two_root/two_root11_degree810.json` (SHA-256 pinned below, the same
pin as `gen_literal131.py`) does not contain the numeric values of its six fixed integers. Nodes
11..16 are symbolic leaves `["coefficient", name]` for `beta K0 MC MF cone_A cone_B`, and the
field `coefficient_binding` names `../coefficients/BINDING.json`, i.e. the file
`scalar/coefficients/BINDING.json` of the package.

The package does not ship that directory in this repository (the intake deduplicated it). The
binding is still pinned twice: the package manifest `MANIFEST_SHA256.json` and the scalar
manifest `scalar/SOURCE_PINS.json` both record the byte count and SHA-256 of
`coefficients/BINDING.json` and of the six `coefficients/*.bin.gz` payloads. This script resolves
each pinned entry to the repository copy with the same name under `COPIES` and requires the same
byte count and SHA-256. Those are the files packages 135, 138, 144 and 172 are bound to, so all
five packages have the same six ports.

The check, link by link, is that of `research/p135-integer11/tools/check_ports135.py`:

1. the JSON's SHA-256 (the pin below and the package manifest's entry), its coefficient leaves
   (names and order) and `coefficient_binding`;
2. the two manifests' `coefficients/BINDING.json` and payload entries: they agree, and a
   repository copy exists with the pinned SHA-256 and size;
3. every payload of `BINDING.json`: gunzip, raw SHA-256, bits, raw bytes, minimal encoding, plus
   the `recipe` strings of the two cones; and the package's own record of the payloads,
   `scalar/COEFFICIENT_RECIPE_CHECK.json`, gives the same raw SHA-256 and bit lengths;
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
PKG = DC / 'con-zfc-diophantine-forms/131-shared-pell-caps-round16'
COPIES = DC / 'candidates/constructive-integer14-quadratic/coefficients'
MANIFEST = ('MANIFEST_SHA256.json',
            'ceef0f13c95002813c0b87879ad86f93c311b43f714bcc93a3707af4c48a1dc5', 'scalar/')
SOURCE_PINS = ('scalar/SOURCE_PINS.json',
               'bee2434e811bf1c673ce8c05bd2706503572ae53d57a7a096215120ad59d2e1f', '')
JSON = ('scalar/two_root/two_root11_degree810.json',
        '4b2eb90c2ce445bc450e4080699d70780da4a86efef5f658696c0caaf84b9fd3')
RECIPE_CHECK = 'scalar/COEFFICIENT_RECIPE_CHECK.json'

spec = importlib.util.spec_from_file_location(
    'check_ports138', DC / 'research/p138-integer11/tools/check_ports138.py')
p138 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p138)
need, PORTS, FAIL = p138.need, p138.PORTS, p138.FAIL
KEYS = ['coefficients/BINDING.json'] + [f'coefficients/{n}.bin.gz' for n in PORTS]


def main():
    print('1. the pinned JSON')
    manifests = {}
    for label, (mpath, msha, prefix) in (('package', MANIFEST), ('scalar', SOURCE_PINS)):
        mdata = (PKG / mpath).read_bytes()
        need(hashlib.sha256(mdata).hexdigest() == msha, f'{mpath} SHA-256 = {msha}')
        manifests[label] = (json.loads(mdata)['files'], prefix)
    name, sha = JSON
    data = (PKG / name).read_bytes()
    need(hashlib.sha256(data).hexdigest() == sha, f'{name} SHA-256 = {sha}')
    pin = manifests['package'][0].get(name)
    need(pin is not None and pin['sha256'] == sha and pin['bytes'] == len(data),
         '  the package manifest pins the same SHA-256 and size')
    p = json.loads(data)
    leaves = [(i, r[1]) for i, r in enumerate(p['nodes']) if r[0] == 'coefficient']
    need([n for _, n in leaves] == PORTS, f'  coefficient leaves, in order: {[n for _, n in leaves]}')
    need([i for i, _ in leaves] == list(range(11, 17)), '  coefficient leaves are nodes 11..16')
    need(not any(r[0] == 'coefficient' and isinstance(r[1], int) for r in p['nodes']),
         '  the JSON carries no numeric value for any coefficient (symbolic leaves only)')
    need(p.get('coefficient_binding') == '../coefficients/BINDING.json',
         f"  coefficient_binding = {p.get('coefficient_binding')!r} (relative to scalar/two_root/)")

    print('2. the manifest pins of scalar/coefficients/, resolved to repository copies')
    copies = {}
    for key in KEYS:
        pins = []
        for label, (manifest, prefix) in manifests.items():
            pin = manifest.get(prefix + key)
            if need(pin is not None, f'the {label} manifest pins {prefix + key}'):
                pins.append((pin['bytes'], pin['sha256']))
        if len(pins) != 2 or not need(pins[0] == pins[1], '  the two manifests agree'):
            continue
        need(not (PKG / 'scalar' / key).exists(), f'  {key} is not shipped in the package directory')
        f = COPIES / Path(key).name
        b = f.read_bytes() if f.exists() else b''
        need(f.exists() and (len(b), hashlib.sha256(b).hexdigest()) == pins[0],
             f'  {key} -> {f.relative_to(DC).as_posix()} ({pins[0][0]} bytes, sha256 {pins[0][1][:16]}...)')
        copies[key] = f
    if len(copies) != len(KEYS) or FAIL:
        print(f'MISMATCH ({len(FAIL)} failures)')
        sys.exit(1)

    print('3. BINDING.json payloads')
    binding = json.loads(copies['coefficients/BINDING.json'].read_text(encoding='utf-8'))
    print(f"  tuple: {binding.get('tuple')!r}; MF convention: {binding.get('MF_convention')!r}")
    recipe = json.loads((PKG / RECIPE_CHECK).read_text(encoding='utf-8'))
    need(recipe.get('status') == 'PASS', f'{RECIPE_CHECK}: status PASS')
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
        rec = recipe['payloads'].get(name, {})
        need(rec.get('raw_sha256') == pin['raw_sha256'] and rec.get('bits') == pin['bits']
             and rec.get('recipe_exact_match') is True,
             f"  {RECIPE_CHECK} records the same raw sha256 and bits for {name}")
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
        'cone_A = 2^1112': lean[:4] + [1 << 1112, lean[5]],
    }
    for name, vals in controls.items():
        need(vals != pay, f'rejected: {name}')

    print('ok' if not FAIL else f'MISMATCH ({len(FAIL)} failures)')
    sys.exit(0 if not FAIL else 1)


if __name__ == '__main__':
    main()
