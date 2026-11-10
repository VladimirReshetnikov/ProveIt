#!/usr/bin/env python3
"""Check that package 138's six ports in Lean are the integers its two JSONs are bound to.

Usage: py -I -X utf8 -B check_ports138.py

What the JSONs pin. `parity_saturated11_native.json` (924/107) and `parity_saturated11_short.json`
(840/108), SHA-256 pinned below (the same pins as `gen_literal.py`), do not contain the numeric
values of their six fixed integers. In both, nodes 11..16 are symbolic leaves
`["coefficient", name]` for `beta K0 MC MF cone_A cone_B`, and the field `coefficient_binding`
names `coefficients/BINDING.json`, a path relative to the package directory. So both forms are
bound to the same six payloads, and to the same Lean ports `P138Ports.ports6`.
The package ships that file and its payloads as restored dependencies:
`integer11/RESTORED_DEPENDENCIES.json` maps `coefficients/BINDING.json` and the six
`coefficients/*.bin.gz` to repository copies, with SHA-256 and byte counts. `BINDING.json` gives
each payload's file name, raw SHA-256, bit length and raw byte length.

The check, link by link:

1. each JSON's SHA-256, its coefficient leaves (names and order) and `coefficient_binding`;
2. every `coefficients/` entry of `RESTORED_DEPENDENCIES.json`: the repository copy exists and
   has the pinned SHA-256 and size;
3. every payload of `BINDING.json`: gunzip, raw SHA-256, bits, raw bytes, minimal encoding;
   plus the `recipe` strings of the two cones;
4. the Lean side: the defining lines of `Source34Ports`, `Source34Kernel`, `Mixed121Kernel`,
   `CompactListMask`, `CompactSymbolicPorts` and `P138Ports` are checked verbatim against the
   transcription below (drift guard), the 943 tile rows are read from `Compact943Data.lean`, and
   `P138Ports.ports6 0..5` are evaluated in Python from that transcription;
5. `ports6 i` equals payload `i` (in the JSON's coefficient order) as integers, and its minimal
   little-endian bytes have the pinned raw SHA-256.

This is finite external evidence for the binding, not a Lean theorem.
"""
from pathlib import Path
import gzip, hashlib, json, re, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
REPO = HERE.parents[5]
PKG = DC / 'con-zfc-diophantine-forms/138-semantic-signs/integer11'
JSONS = [
    (PKG / 'parity_saturated11_native.json',
     'ae109bcc44bd2d6c7102875eb79e562366bbf46ce1e350d0cfa8cc026add4195'),
    (PKG / 'parity_saturated11_short.json',
     '286116717dcd19faaec9f27e2a88e36a704a1a644385c1a3a9116c564994cfe7'),
]
LEAN = DC / 'Lean/DiophantineConsistency'
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']

FAIL = []


def need(ok, msg):
    print(('  ok   ' if ok else '  FAIL ') + msg)
    if not ok:
        FAIL.append(msg)
    return ok


# --- 4. Lean drift guard: exact definition text that the transcription below implements ------
LEAN_TEXT = {
    'Source34/Source34Ports.lean': [
        'def radix : ℕ := 2^121',
        'def betaNat : ℕ := 2^(121*8801) - 1',
        'def maskSupport : Finset ℕ := (Source34Kernel.support.filter (· ≠ 1)).toFinset',
        'def lowNat : ℕ := Nat.ofDigits radix (CompactListMask.digits radix 8801 1063 maskSupport)',
        'def mu : ℕ := 1022 + ∑ j ∈ Finset.range 44, Mixed121Kernel.W j',
        'def padding : ℕ := 2^119 - 1',
        'def lastPadding : ℕ := 2^27 - 1',
        'def track : List ℕ := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0]',
        'def highInit : List ℕ :=\n'
        '  [4] ++ List.replicate 999 0 ++ track ++ [0] ++ track ++ List.replicate 1154 0 ++ [1] ++\n'
        '  List.replicate 1100 0 ++ [1] ++\n'
        '  List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++\n'
        '  List.replicate 3296 0 ++ List.replicate 7 padding ++ [lastPadding]',
        'def highDigits : List ℕ := highInit ++ [0]',
        'def highNat : ℕ := Nat.ofDigits radix highDigits',
        'def ports : Fin 4 → ℕ :=\n'
        '  CompactSymbolicPorts.ports betaNat (Source34Kernel.paramKernel Mixed121Kernel.rho) lowNat highNat',
    ],
    'Compact44/CompactSymbolicPorts.lean': [
        'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]',
    ],
    'Source34/Source34Kernel.lean': [
        'def extraPositions : List ℕ :=\n'
        '  (List.range 10).map (1020 + 2 * ·) ++ (List.range 10).map (1000 + 2 * ·) ++\n'
        '    (List.range 10).map (980 + 2 * ·) ++ (List.range 10).map (960 + 2 * ·) ++\n'
        '    [1095, 1096, 2195, 3296]',
        'def paramKernel (r : ℕ) : ℕ :=\n'
        '  r^40+r^41+r^1100+r^2200 +\n'
        '  (∑ i : Fin 943, clause (Compact943Data.row i) * (r^(4393-i.val)+r^(5495-i.val))) +\n'
        '  (∑ k : Fin 44, W k.val * (r^(4393-extraPos k)+r^(5495-extraPos k))) +\n'
        '  r^8801*r^1',
        'def support : List ℕ :=\n'
        '  List.range 943 ++ (List.range 40).map (960 + 2 * ·) ++\n'
        '    [1063, 1064, 1095, 1096, 2195, 3296]',
        'open Mixed121Kernel (W clause',
    ],
    'Mixed121/Mixed121Kernel.lean': [
        'def rho : ℕ := 2^121',
        'def W (j : ℕ) : ℕ := 2^(10+2*j)',
        'def field (x t : ℕ) : ℕ := ∑ j : Fin 10, ((x+512)/2^j.val % 2) * W (10*t+j.val)',
        'def clause (tile : ℕ × ℕ × ℕ × ℕ) : ℕ :=\n'
        '  1 + field tile.1 0 + field tile.2.1 1 + field tile.2.2.1 2 + field tile.2.2.2 3 +\n'
        '    W 40 + W 41 + W 42 + W 43',
    ],
    'Compact44/CompactListMask.lean': [
        'def digit (B special : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=\n'
        '  if j=special then B-4 else if j∈S then B-2 else B-1',
        'def digits (B len special : ℕ) (S : Finset ℕ) : List ℕ :=\n'
        '  (List.range len).map (digit B special S)',
    ],
    'Compact44/Compact943Data.lean': [
        'def row (i : Fin 943) : Nat × Nat × Nat × Nat :=\n'
        '  rows.get ⟨i.val, by simpa only [rows_length] using i.isLt⟩',
    ],
    'P138/P138Ports.lean': [
        'def coneA : ℕ := 2^1113',
        'def coneB : ℕ := 2^666104',
        'def vec6 (a b c d e f : ℕ) : Fin 6 → ℕ := ![a, b, c, d, e, f]',
        'def ports6 : Fin 6 → ℕ :=\n'
        '  vec6 (Source34Ports.ports 0) (Source34Ports.ports 1) (Source34Ports.ports 2)\n'
        '    (Source34Ports.ports 3) coneA coneB',
    ],
}


def lean_rows():
    text = (LEAN / 'Compact44/Compact943Data.lean').read_text(encoding='utf-8')
    body = text.split('-- BEGIN PINNED ORDERED ROWS')[1].split('-- END PINNED ORDERED ROWS')[0]
    return [tuple(map(int, m)) for m in re.findall(r'\((\d+), (\d+), (\d+), (\d+)\)', body)]


# --- the transcription of the Lean definitions ----------------------------------------------
RHO_BITS, L = 121, 8801
RHO = 1 << RHO_BITS


def rpow(e):            # rho^e
    return 1 << (RHO_BITS * e)


def W(j):
    return 1 << (10 + 2 * j)


def field(x, t):
    return sum(((x + 512) >> j & 1) * W(10 * t + j) for j in range(10))


def clause(tile):
    return (1 + field(tile[0], 0) + field(tile[1], 1) + field(tile[2], 2) + field(tile[3], 3)
            + W(40) + W(41) + W(42) + W(43))


def extra_positions():
    return ([1020 + 2 * j for j in range(10)] + [1000 + 2 * j for j in range(10)]
            + [980 + 2 * j for j in range(10)] + [960 + 2 * j for j in range(10)]
            + [1095, 1096, 2195, 3296])


def param_kernel(rows):
    ep = extra_positions()
    assert len(ep) == 44
    return (rpow(40) + rpow(41) + rpow(1100) + rpow(2200)
            + sum(clause(rows[i]) * (rpow(4393 - i) + rpow(5495 - i)) for i in range(943))
            + sum(W(k) * (rpow(4393 - ep[k]) + rpow(5495 - ep[k])) for k in range(44))
            + rpow(8801) * rpow(1))


def support():
    return list(range(943)) + [960 + 2 * j for j in range(40)] + [1063, 1064, 1095, 1096, 2195, 3296]


def of_digits(ds):      # Nat.ofDigits RHO ds (little-endian digit list)
    v = 0
    for d in reversed(ds):
        v = v * RHO + d
    return v


def low_nat():
    S = set(e for e in support() if e != 1)
    digit = lambda j: RHO - 4 if j == 1063 else RHO - 2 if j in S else RHO - 1
    return of_digits([digit(j) for j in range(L)])


def high_nat():
    mu = 1022 + sum(W(j) for j in range(44))
    padding, last = (1 << 119) - 1, (1 << 27) - 1
    track = [1, 0] * 10
    rep = lambda n, x: [x] * n
    init = ([4] + rep(999, 0) + track + [0] + track + rep(1154, 0) + [1]
            + rep(1100, 0) + [1]
            + rep(1096, 0) + [mu] + rep(1101, 0) + [mu]
            + rep(3296, 0) + rep(7, padding) + [last])
    assert len(init) == 8800
    digits = init + [0]
    assert len(digits) == L and all(d < RHO for d in digits)
    return of_digits(digits)


def ports6(rows):
    beta = (1 << (121 * 8801)) - 1
    K = param_kernel(rows)
    low, high = low_nat(), high_nat()
    return [beta, K, low, beta + high, 1 << 1113, 1 << 666104]


def raw(v):
    return v.to_bytes((v.bit_length() + 7) // 8, 'little')


def main():
    print('1. the pinned JSONs')
    for json_path, json_sha256 in JSONS:
        data = json_path.read_bytes()
        need(hashlib.sha256(data).hexdigest() == json_sha256, f'{json_path.name} SHA-256 = {json_sha256}')
        p = json.loads(data)
        leaves = [(i, r[1]) for i, r in enumerate(p['nodes']) if r[0] == 'coefficient']
        need([n for _, n in leaves] == PORTS, f'  coefficient leaves, in order: {[n for _, n in leaves]}')
        need([i for i, _ in leaves] == list(range(11, 17)), '  coefficient leaves are nodes 11..16')
        need(not any(r[0] == 'coefficient' and isinstance(r[1], int) for r in p['nodes']),
             '  the JSON carries no numeric value for any coefficient (symbolic leaves only)')
        need(p.get('coefficient_binding') == 'coefficients/BINDING.json',
             f"  coefficient_binding = {p.get('coefficient_binding')!r}")

    print('2. the restored dependencies of coefficients/')
    restored = json.loads((PKG / 'RESTORED_DEPENDENCIES.json').read_text(encoding='utf-8'))
    copies = {}
    binding_entry = restored.get('coefficients/BINDING.json')
    need(binding_entry is not None, 'RESTORED_DEPENDENCIES maps coefficients/BINDING.json')
    for key, pin in sorted(restored.items()):
        if not key.startswith('coefficients/') or key.startswith('coefficients/recipe/'):
            continue
        f = REPO / pin['repository_path']
        b = f.read_bytes() if f.exists() else b''
        need(f.exists() and len(b) == pin['bytes'] and hashlib.sha256(b).hexdigest() == pin['sha256'],
             f"{key} -> {pin['repository_path']} ({pin['bytes']} bytes, sha256 {pin['sha256'][:16]}...)")
        copies[key] = f

    print('3. BINDING.json payloads')
    binding = json.loads(copies['coefficients/BINDING.json'].read_text(encoding='utf-8'))
    print(f"  tuple: {binding.get('tuple')!r}; MF convention: {binding.get('MF_convention')!r}")
    payloads = {}
    for name in PORTS:
        pin = binding['payloads'][name]
        key = 'coefficients/' + pin['file']
        need(key in copies, f'{name}: payload file {key} is a pinned restored dependency')
        rawb = gzip.decompress(copies[key].read_bytes())
        v = int.from_bytes(rawb, 'little')
        ok = (hashlib.sha256(rawb).hexdigest() == pin['raw_sha256'] and v.bit_length() == pin['bits']
              and len(rawb) == pin['raw_bytes'] and raw(v) == rawb)
        need(ok, f"{name}: {pin['file']} raw sha256/bits ({pin['bits']})/bytes/minimal encoding")
        payloads[name] = v
    need(binding['payloads']['cone_A'].get('recipe') == '2**1113', 'cone_A recipe string is 2**1113')
    need(binding['payloads']['cone_B'].get('recipe') == '2**666104', 'cone_B recipe string is 2**666104')

    print('4. the Lean definitions (verbatim) and their evaluation')
    for rel, snippets in LEAN_TEXT.items():
        text = (LEAN / rel).read_text(encoding='utf-8').replace('\r\n', '\n')
        for s in snippets:
            need(s in text, f'{rel}: {s.splitlines()[0]}')
    rows = lean_rows()
    need(len(rows) == 943, f'Compact943Data rows: {len(rows)}')
    lean = ports6(rows)

    print('5. Lean ports6 i = payload i')
    for i, name in enumerate(PORTS):
        v = lean[i]
        src = (f'Source34Ports.ports {i}' if i < 4 else ('coneA = 2^1113' if i == 4 else 'coneB = 2^666104'))
        need(v == payloads[name] and hashlib.sha256(raw(v)).hexdigest() == binding['payloads'][name]['raw_sha256'],
             f'ports6 {i} ({src}, {v.bit_length()} bits) = {name} payload')
    need(lean[4] == 2 ** 1113 and lean[5] == 2 ** 666104, 'ports6 4 = 2^1113 and ports6 5 = 2^666104')

    print('6. mutation controls (each must be rejected)')
    pay = [payloads[n] for n in PORTS]
    swapped = lambda a, b: [lean[b] if i == a else lean[a] if i == b else lean[i] for i in range(6)]
    controls = {
        'MC and MF swapped': swapped(2, 3),
        'cones swapped': swapped(4, 5),
        'MF unshifted (MF_native)': [lean[i] - (lean[0] if i == 3 else 0) for i in range(6)],
        'beta off by one (2^1064921)': [lean[0] + 1] + lean[1:],
        'cone_A = 2^1112': lean[:4] + [1 << 1112, lean[5]],
        'K0 with one tile row changed': [lean[0], param_kernel([(rows[0][0] + 1,) + rows[0][1:]] + rows[1:])]
                                        + lean[2:],
    }
    for name, vals in controls.items():
        need(vals != pay, f'rejected: {name}')

    print('ok' if not FAIL else f'MISMATCH ({len(FAIL)} failures)')
    sys.exit(0 if not FAIL else 1)


if __name__ == '__main__':
    main()
