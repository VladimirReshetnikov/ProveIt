#!/usr/bin/env python3
"""Fixed integer witness against canonical-endpoint Waterfall count summaries.

Read-only, standard-library replay. No supplied Python module is imported.
verify(archive=...) safely extracts a pinned archive into a temporary directory;
verify(source_root=...) accepts an already extracted, member-pinned tree.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import tempfile
import zipfile

ARCHIVE_SHA256 = 'b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc'
SOURCE_PINS = {
    'source/UniversalTM15x2.twm.txt': '52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a',
    'source/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae',
    'replay/verify_frontend.py': '951c3482067c6754f23f3ad4cf21e13efe32f51ec9eed599bce02cac6117589d',
    'paper/waterfall-diophantine.tex': '22d6fc7aa755dcd3f6043f1b7472a82f6df2221bc3b21582a9c0fa76372a4e2f',
}
NAMES = (['LeftTape', 'LeftTemp', 'LeftTrans', 'LeftDiv0', 'LeftDiv1',
          'LeftMult', 'LeftWrite0', 'LeftWrite1']
         + [f'Trans{chr(65+q)}{s}' for q in range(15) for s in range(2)]
         + ['RightWrite0', 'RightWrite1', 'RightMult', 'RightDiv0',
            'RightDiv1', 'RightTrans', 'RightTemp', 'RightTape'])
INDEX = {name: i for i, name in enumerate(NAMES)}
HALT = INDEX['TransJ1']
EXTRA = {
    'LeftTape': 10, 'LeftTemp': 10, 'LeftDiv0': 1,
    'LeftWrite0': 6, 'LeftWrite1': 1,
    'TransA0': 1, 'TransB0': 1, 'TransC0': 1, 'TransG0': 1,
    'TransH0': 1, 'TransI0': 1, 'TransN1': 2, 'TransO0': 2,
    'RightWrite0': 2, 'RightWrite1': 1, 'RightDiv0': 1,
    'RightTemp': 10, 'RightTape': 10,
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def canonical(state, symbol, left, right):
    require(type(state) is int and 0 <= state < 15, 'state domain')
    require(type(symbol) is int and symbol in (0, 1), 'symbol domain')
    require(type(left) is int and left >= 0 and type(right) is int and right >= 0,
            'natural half tapes')
    d = [2] * 46
    d[INDEX['LeftTape']] = 2 + 2 * left
    d[INDEX['RightTape']] = 2 + 2 * right
    for direction in ('Left', 'Right'):
        for t in (0, 1):
            d[INDEX[f'{direction}Div{t}']] = 2 + int(t != symbol)
    for q in range(15):
        for t in (0, 1):
            d[INDEX[f'Trans{chr(65+q)}{t}']] = 1 + int(q != state) + int(t != symbol)
    return d

def matrix_action(rows, counts):
    require(len(counts) == 46 and all(type(x) is int and x >= 0 for x in counts),
            'natural counts')
    return [sum(rows[i][j] * counts[i] for i in range(46)) for j in range(46)]

def independent_event_run(rows, initial, cap=1000):
    d = list(initial)
    counts = [0] * 46
    events = []
    while True:
        timestamp = min(d)
        active = [i for i, value in enumerate(d) if value == timestamp]
        require(len(active) == 1, 'undefined minimum tie')
        i = active[0]
        if i == HALT:
            return d, counts, events, timestamp
        require(len(events) < cap, 'event cap exceeded')
        require(not events or timestamp > events[-1]['timestamp'], 'event time not increasing')
        events.append({'clock': NAMES[i], 'timestamp': timestamp})
        counts[i] += 1
        d = [x + y for x, y in zip(d, rows[i])]

def _verify_tree(root):
    root = Path(root)
    for name, expected in SOURCE_PINS.items():
        require(digest((root / name).read_bytes()) == expected, 'source hash mismatch: ' + name)
    serialized = json.loads((root / 'source/UniversalTM15x2.twm.txt').read_text())
    require(type(serialized) is list and len(serialized) == 47, 'matrix outer schema')
    require(all(type(r) is list and len(r) == 47 and
                all(type(x) is int and x >= 0 for x in r) for r in serialized),
            'matrix row schema')
    rows = [r[1:] for r in serialized[1:]]
    require(serialized[0] == [47] + [46] * 46, 'serialization metadata')
    require([r[0] for r in serialized[1:]] == canonical(0, 0, 0, 0), 'base loader')
    require([i for i, r in enumerate(rows) if not any(r)] == [HALT], 'halt source')
    require(all(rows[i][i] > 0 for i in range(46) if i != HALT), 'positive self resets')
    initial = canonical(0, 0, 6, 0)
    final, base, events, tau = independent_event_run(rows, initial)
    controls = sum(base[8:38])
    require((sum(base), controls, tau) == (189, 7, 428), 'actual first halt accounting')
    require(final == [a + b for a, b in zip(initial, matrix_action(rows, base))],
            'actual source matrix endpoint')
    shift = tau - 1
    norm = [x - shift for x in final]
    left_twice = norm[INDEX['LeftTape']] - 2
    right_twice = norm[INDEX['RightTape']] - 2
    require(left_twice >= 0 and right_twice >= 0 and
            left_twice % 2 == right_twice % 2 == 0, 'terminal tape decoding')
    left, right = left_twice // 2, right_twice // 2
    require(norm == canonical(9, 1, left, right), 'full canonical halt endpoint')
    extra = [EXTRA.get(name, 0) for name in NAMES]
    delta = matrix_action(rows, extra)
    require(delta == [194] * 46, 'literal common-shift identity')
    require((sum(extra), sum(extra[8:38]), extra[HALT]) == (62, 10, 0), 'extra accounting')
    require(194 == 2 * sum(extra) + 7 * sum(extra[8:38]), 'extra potential identity')
    false_counts = [a + b for a, b in zip(base, extra)]
    false_final = [a + b for a, b in zip(initial, matrix_action(rows, false_counts))]
    require(false_final == [x + 194 for x in final], 'shifted endpoint identity')
    require(false_final == [x + 621 for x in canonical(9, 1, left, right)],
            'shifted canonical endpoint')
    require(min(false_final) == 622 and false_final[HALT] == 622 and
            all(false_final[i] > 622 for i in range(46) if i != HALT), 'strict halt endpoint order')
    require((sum(false_counts), sum(false_counts[8:38])) == (251, 17), 'false count accounting')
    require(622 == 1 + 2 * 251 + 7 * 17, 'false timestamp identity')
    # A concise independent potential check for every source column.
    weights = [288 if n in ('LeftTrans', 'RightTrans') else
               -373 if 'Div' in n else 970 if 'Mult' in n else
               -4 if 'Write' in n else 0 for n in NAMES]
    require(sum(weights) == 1008, 'weight sum')
    require(sum(a*b for a,b in zip(weights, initial)) == 1270, 'initial potential')
    for i, row in enumerate(rows):
        expected = 0 if i == HALT else 2016 + 7056 * int(8 <= i < 38)
        require(sum(a*b for a,b in zip(weights, row)) == expected, 'column potential')
    return {
        'status': 'PASS', 'source_pins': SOURCE_PINS,
        'scope': 'Counterexample to canonical endpoint plus nonnegative event counts and timing accounting; not the full bounded-history polynomial.',
        'initial': {'state': 'A', 'symbol': 0, 'left': 6, 'right': 0, 'deadlines': initial},
        'clock_order': NAMES,
        'actual': {'events': 189, 'control_firings': 7, 'halt_timestamp': 428,
                   'counts': base, 'final_deadlines': final,
                   'terminal_state': 'J', 'terminal_symbol': 1,
                   'terminal_left': left, 'terminal_right': right,
                   'strict_event_trace': events},
        'extra': {'nonzero_counts': EXTRA, 'counts': extra, 'matrix_action': delta,
                  'events': 62, 'control_firings': 10, 'common_shift': 194},
        'false_endpoint': {'counts': false_counts, 'final_deadlines': false_final,
                           'events': 251, 'control_firings': 17, 'halt_timestamp': 622,
                           'strict_unique_halt_minimum': True,
                           'same_terminal_half_tapes': True,
                           'actual_first_halt_still': 428},
        'checked': {'source_columns': 46, 'matrix_action_coordinates': 46,
                    'actual_nonhalt_event_selections': 189,
                    'actual_halt_observations': 1,
                    'false_endpoint_order_comparisons': 45,
                    'potential_source_columns': 46},
        'family': {'n_domain': 'natural', 'counts': 'base+n*extra',
                   'events': '189+62*n', 'control_firings': '7+10*n',
                   'halt_timestamp': '428+194*n',
                   'false_for': 'every n>=1'},
    }

def verify(*, archive=None, source_root=None):
    require((archive is None) != (source_root is None), 'supply exactly one source')
    if source_root is not None:
        return _verify_tree(source_root)
    archive = Path(archive)
    require(digest(archive.read_bytes()) == ARCHIVE_SHA256, 'archive hash mismatch')
    with tempfile.TemporaryDirectory(prefix='waterfall-endpoint-alias-') as temp:
        with zipfile.ZipFile(archive) as z:
            seen = set()
            for info in z.infolist():
                p = PurePosixPath(info.filename)
                require(not p.is_absolute() and p.parts and '..' not in p.parts and
                        '\\' not in info.filename and str(p) not in seen,
                        'unsafe/duplicate archive path')
                require(not stat.S_ISLNK(info.external_attr >> 16), 'archive symlink')
                seen.add(str(p))
                target = Path(temp).joinpath(*p.parts)
                if info.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(z.read(info))
        result = _verify_tree(Path(temp) / 'waterfall-diophantine')
    result['archive_sha256'] = ARCHIVE_SHA256
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--archive', type=Path)
    group.add_argument('--source-root', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = verify(archive=args.archive, source_root=args.source_root)
    if args.expect:
        require(result == json.loads(args.expect.read_text()), 'saved receipt mismatch')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')

if __name__ == '__main__':
    main()
