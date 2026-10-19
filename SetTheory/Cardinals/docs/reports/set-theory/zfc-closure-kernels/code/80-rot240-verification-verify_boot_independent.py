"""Independent sparse and dense blank initialization with the local clock.

This checker reads the packaged tables and mapping; only its evidence
receipt is written. It does not regenerate or overwrite machine artifacts.
"""
from pathlib import Path
import argparse, hashlib, json, sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run with assertions enabled; -O is not accepted')
DEFAULT_ROOT = Path(__file__).resolve().parents[1]
PINS = {
    'reference/rotated241_old.tm':
        '88a1f42b01b7e2b4bf29bc1b3819b78f1e7a17cefaefbc003654f2f5cc202c2f',
    'machines/zfc240_old.tm':
        '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f',
    'machines/zfc240.tm':
        '508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd',
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        assert key not in table and d in ('L', 'R')
        assert int(b) in (0, 1) and int(w) in (0, 1)
        table[key] = int(w), (1 if d == 'R' else -1), int(z)
    return table


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output is None:
        args.output = args.root / 'evidence' / 'boot_independent.json'
    for name, expected in PINS.items():
        assert digest(args.root / name) == expected
    old = read(args.root / 'reference' / 'rotated241_old.tm')
    new = read(args.root / 'machines' / 'zfc240_old.tm')
    canonical = read(args.root / 'machines' / 'zfc240.tm')
    assert len(old) == 482 and len(new) == len(canonical) == 480
    mapping = json.loads((args.root / 'machines' / 'renumbering.json').read_text())
    rename = {int(q): z for q, z in mapping['old_to_new'].items()}
    assert {key: value for key, value in mapping.items() if key != 'old_to_new'} == {
        'start': 0, 'dispatcher': 84, 'halt': 240,
    }
    assert rename[95] == 0 and rename[96] == 84 and rename[254] == 240
    assert {(rename[q], b): (w, d, rename[z])
            for (q, b), (w, d, z) in new.items()} == canonical

    keys = ((72, 0), (72, 1), (90, 0), (90, 1))
    counts = {key: 0 for key in keys}
    ones, q, h = set(), 95, 0
    for tick in range(408941):
        b = int(h in ones)
        if (q, b) in counts:
            counts[q, b] += 1
        w, d, q = old[q, b]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    assert (q, h, len(ones)) == (96, -5, 351)
    wanted_ones, position = {-6, 176}, 177
    for value in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
        position += 1
        wanted_ones.update(range(position, position + value + 1))
        position += value + 1
    assert ones == wanted_ones
    assert counts == {(72, 0): 74, (72, 1): 37, (90, 0): 18, (90, 1): 24}
    extra = 8 * counts[72, 0] + 2 * (counts[72, 1] + counts[90, 0] + counts[90, 1])
    new_ticks = 408941 + extra
    assert extra == 750 and new_ticks == 409691

    ones, q, h = set(), 95, 0
    for tick in range(new_ticks):
        w, d, q = new[q, int(h in ones)]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    assert (q, h, ones) == (96, -5, wanted_ones)

    dense, lo, q, h = bytearray(1), 0, 0, 0
    for tick in range(new_ticks):
        if h < lo:
            dense = bytearray(lo - h) + dense
            lo = h
        if h >= lo + len(dense):
            dense.extend(bytearray(h - lo - len(dense) + 1))
        w, d, q = canonical[q, dense[h - lo]]
        dense[h - lo] = w
        h += d
    assert (q, h, {lo + i for i, b in enumerate(dense) if b}) == (84, -5, wanted_ones)

    result = {
        'status': 'PASS_EXACT_240_BLANK_SPARSE_DENSE',
        'reference_rotated241_steps': 408941,
        'candidate240_steps': new_ticks,
        'extra_steps': extra,
        'reference_exceptional_visits': {f'{q}/{b}': counts[q, b] for q, b in keys},
        'old_label_dispatcher': 96,
        'canonical_dispatcher': 84,
        'head': -5,
        'marker': -6,
        'header': 176,
        'ones': 351,
        'zero_exterior': True,
        'same_complete_tape': True,
        'logical_registers': [3, 0, 0, 0, 3, 0, 0, 0, 0],
        'spare_blocks': 167,
        'spare_block_values': 1,
        'candidate_inherited_sha256': PINS['machines/zfc240_old.tm'],
        'candidate_canonical_sha256': PINS['machines/zfc240.tm'],
        'checker_sha256': digest(Path(__file__)),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
