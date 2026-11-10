#!/usr/bin/env python3
"""Check that the six ports of package 137's weak product 648/115 equation are `P138Ports.ports6`.

Usage: py -I -X utf8 -B check_ports137.py

What the JSON pins. `integer/weak_product11_none.json` (SHA-256 pinned below, the same pin as
`gen_literal137.py`) does not contain the numeric values of its six fixed integers. Nodes 11..16
are symbolic leaves `["coefficient", name]` for `beta K0 MC MF cone_A cone_B`, and the field
`coefficient_binding` names `coefficients/BINDING.json`, i.e. the file
`integer/coefficients/BINDING.json` of the package.

The package does not ship that directory in this repository (the intake deduplicated it). The
binding is still pinned three times: the release manifest `MANIFEST.json` (a list of
`{path, bytes, sha256}` rows, paths prefixed `integer/`), the manifest `integer/MANIFEST.json`
and the dependency pins `integer/SOURCE_PINS.json` all record the byte count and SHA-256 of
`coefficients/BINDING.json` and of the six `coefficients/*.bin.gz` payloads. This script resolves
each pinned entry to the repository copy with the same name under `COPIES` and requires the same
byte count and SHA-256. Those are the files packages 131, 135, 138, 144 and 172 are bound to, so
all six packages have the same six ports.

The check, link by link:

1. the JSON's SHA-256 (the pin below and the entries of the two manifests that list it), its
   coefficient leaves (names and order) and `coefficient_binding`;
2. the three pin sets' `coefficients/BINDING.json` and payload entries: they agree, and a
   repository copy exists with the pinned SHA-256 and size;
3. every payload of `BINDING.json`: gunzip, raw SHA-256, bits, raw bytes, minimal encoding, plus
   the `recipe` strings of the two cones; and the package's own record `integer/CHECK.json`
   (pinned by both manifests): status, the two coefficient flags, the topology it records for
   this equation, and `beta = 2^d - 1` for the `d` of its recipe audit;
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
PKG = DC / 'con-zfc-diophantine-forms/137-odd-helpers-saturated-carriers'
COPIES = DC / 'candidates/constructive-integer14-quadratic/coefficients'
# (label, path, SHA-256, key of the pin table, path prefix of the integer/ entries)
PINSETS = [
    ('release', 'MANIFEST.json',
     '49f87b1bd4270a0721affd6cda5f7899343732ba0ea563d84dc713bc3a4d94e7', 'files', 'integer/'),
    ('integer', 'integer/MANIFEST.json',
     '4d0f9e632daa027bb569746865ddc6a39cc5e2d1bfe9df5396a17941c329c666', 'files', ''),
    ('source', 'integer/SOURCE_PINS.json',
     '6a0326ceee80512e70520faf27d1978e5e6d8fa1d4bcbed010069ff028ea23a1', 'dependencies', ''),
]
NAME = 'weak_product11_none'
JSON = ('integer/weak_product11_none.json',
        '63023b059a84ced728fae1dddfcc334a5b8c401abc77a0012266d77a28b4f963')
CHECK = ('integer/CHECK.json',
         '0bd158ab64c86635a7b1376c8e67027c1e88e2aa58ee1b919025609547a3d7db')
TOPOLOGY = {'live_nodes': 140, 'operations': 115,
            'counts': {'mul': 73, 'add': 23, 'sub': 19}, 'syntactic_degree': 648}

spec = importlib.util.spec_from_file_location(
    'check_ports138', DC / 'research/p138-integer11/tools/check_ports138.py')
p138 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p138)
need, PORTS, FAIL = p138.need, p138.PORTS, p138.FAIL
KEYS = ['coefficients/BINDING.json'] + [f'coefficients/{n}.bin.gz' for n in PORTS]


def pin_table(raw, key):
    """A pin set as {path: (bytes, sha256)}; the release manifest is a list of rows."""
    table = json.loads(raw)[key]
    if isinstance(table, list):
        rows = {r['path']: (r['bytes'], r['sha256']) for r in table}
        need(len(rows) == len(table), '  the release manifest lists every path once')
        return rows
    return {k: (v['bytes'], v['sha256']) for k, v in table.items()}


def main():
    print('1. the pinned JSON')
    pins = {}
    for label, mpath, msha, key, prefix in PINSETS:
        mdata = (PKG / mpath).read_bytes()
        need(hashlib.sha256(mdata).hexdigest() == msha, f'{mpath} SHA-256 = {msha}')
        pins[label] = (pin_table(mdata, key), prefix)
    for name, sha in (JSON, CHECK):
        data = (PKG / name).read_bytes()
        need(hashlib.sha256(data).hexdigest() == sha, f'{name} SHA-256 = {sha}')
        for label in ('release', 'integer'):
            table, prefix = pins[label]
            rel = prefix + name[len('integer/'):]
            need(table.get(rel) == (len(data), sha),
                 f'  the {label} manifest pins the same SHA-256 and size ({rel})')
    p = json.loads((PKG / JSON[0]).read_bytes())
    need(p.get('name') == NAME, f'  name = {NAME}')
    leaves = [(i, r[1]) for i, r in enumerate(p['nodes']) if r[0] == 'coefficient']
    need([n for _, n in leaves] == PORTS, f'  coefficient leaves, in order: {[n for _, n in leaves]}')
    need([i for i, _ in leaves] == list(range(11, 17)), '  coefficient leaves are nodes 11..16')
    need(not any(r[0] == 'coefficient' and isinstance(r[1], int) for r in p['nodes']),
         '  the JSON carries no numeric value for any coefficient (symbolic leaves only)')
    need(p.get('coefficient_binding') == 'coefficients/BINDING.json',
         f"  coefficient_binding = {p.get('coefficient_binding')!r} (relative to integer/)")

    print('2. the pins of integer/coefficients/, resolved to repository copies')
    copies = {}
    for key in KEYS:
        got = []
        for label, (table, prefix) in pins.items():
            pin = table.get(prefix + key)
            if need(pin is not None, f'the {label} pin set pins {prefix + key}'):
                got.append(pin)
        if len(got) != len(PINSETS) or not need(len(set(got)) == 1, '  the three pin sets agree'):
            continue
        need(not (PKG / 'integer' / key).exists(), f'  {key} is not shipped in the package directory')
        f = COPIES / Path(key).name
        b = f.read_bytes() if f.exists() else b''
        need(f.exists() and (len(b), hashlib.sha256(b).hexdigest()) == got[0],
             f'  {key} -> {f.relative_to(DC).as_posix()} ({got[0][0]} bytes, sha256 {got[0][1][:16]}...)')
        copies[key] = f
    if len(copies) != len(KEYS) or FAIL:
        print(f'MISMATCH ({len(FAIL)} failures)')
        sys.exit(1)

    print('3. BINDING.json payloads')
    binding = json.loads(copies['coefficients/BINDING.json'].read_text(encoding='utf-8'))
    print(f"  tuple: {binding.get('tuple')!r}; MF convention: {binding.get('MF_convention')!r}")
    payloads = {}
    for name in PORTS:
        pin = binding['payloads'][name]
        key = 'coefficients/' + pin['file']
        need(key in copies, f'{name}: payload file {key} is a pinned copy')
        rawb = gzip.decompress(copies[key].read_bytes())
        v = int.from_bytes(rawb, 'little')
        ok = (hashlib.sha256(rawb).hexdigest() == pin['raw_sha256'] and v.bit_length() == pin['bits']
              and len(rawb) == pin['raw_bytes'] and p138.raw(v) == rawb)
        need(ok, f"{name}: {pin['file']} raw sha256/bits ({pin['bits']})/bytes/minimal encoding")
        payloads[name] = v
    need(binding['payloads']['cone_A'].get('recipe') == '2**1113', 'cone_A recipe string is 2**1113')
    need(binding['payloads']['cone_B'].get('recipe') == '2**666104', 'cone_B recipe string is 2**666104')
    check = json.loads((PKG / CHECK[0]).read_bytes())
    need(check.get('status') == 'PASS', f'{CHECK[0]}: status PASS')
    need(check.get('all_six_coefficient_payloads_authenticated') is True
         and check.get('full_coefficient_recipe_rebuilt') is True,
         f'  {CHECK[0]} records the six payloads as authenticated and the recipe as rebuilt')
    rows = [e for e in check.get('equations', []) if e.get('name') == NAME]
    need(len(rows) == 1 and rows[0].get('topology') == TOPOLOGY,
         f'  {CHECK[0]} records the topology of {NAME}: {TOPOLOGY}')
    audit = check.get('recipe_audit', {})
    need((audit.get('b'), audit.get('L')) == (121, 8801), '  recipe audit: b = 121, L = 8801')
    need(type(audit.get('d')) is int and payloads['beta'] == (1 << audit['d']) - 1,
         f"  beta = 2^d - 1 for the recipe audit's d = {audit.get('d')}")

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
