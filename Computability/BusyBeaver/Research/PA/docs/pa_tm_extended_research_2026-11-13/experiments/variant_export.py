"""Export a closing-test variant from a bundled native table or discovery JSON.

Run from the package root. --check-only validates the complete constrained
instruction contract suite without writing the larger derived context files.
"""
import argparse
import collections
import hashlib
import json
import sys
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE / 'verification'))
from core import *


def bundled_variant(register):
    path = PACKAGE / 'auxiliary196' / f'pa196_close_cd{register}.native.tm'
    raw = path.read_bytes()
    rows = {}
    for line in raw.decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        assert bit in (0, 1) and write in (0, 1) and direction in ('L', 'R')
        assert (q, bit) not in rows
        rows[q, bit] = (write, direction == 'R', target)
    original, _ = machine()
    assert set(rows) == set(original) and len(rows) == 392
    assert {key for key in rows if rows[key] != original[key]} == {(1365, 1)}
    sites, instructions = program()
    sites, instructions = list(sites), list(instructions)
    at = 3692
    p, op, arg = sites[at]
    assert (op, arg) == ('breakTo', 1)
    assert instructions[at][0] == 'jump'
    zero_target = instructions[at][1]

    # A decrement's zero branch leaves the nearest left-child scope, just as
    # breakTo 1 does. Its positive branch goes to the next source leaf.
    def locate(prefix):
        for i, (q, _, _) in enumerate(sites):
            if q[:len(prefix)] == prefix or (
                prefix[:len(q)] == q and not any(prefix[len(q):])
            ):
                return i
        raise ValueError(('missing source prefix', prefix))

    def after(prefix):
        prefix = list(prefix)
        for i in range(len(prefix) - 1, -1, -1):
            if prefix[i] == 0:
                prefix[i] = 1
                return locate(tuple(prefix[:i + 1]))
        raise ValueError(('source exit', prefix))

    positive_target = after(p)
    sites[at] = (p, 'dec', register)
    instructions[at] = ('dec', register, zero_target, positive_target)
    assert zero_target == 3799 and positive_target == 3693
    return {
        'meta': {
            'register': register,
            'native_table': path.name,
            'native_sha256': hashlib.sha256(raw).hexdigest(),
            'source_basis': 'verification/core.py program()',
            'source_change': 'Only site 3692: breakTo 1 -> dec register',
            'precondition': 'Logical registers 3 through 7 are zero after the final AX guard.',
        },
        'rows': [[q, b, *act] for (q, b), act in sorted(rows.items())],
        'source_sites': sites,
        'instructions': instructions,
        'zero_constrained_sites': [at],
    }


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('json_file', nargs='?', help='Optional original discovery JSON file')
parser.add_argument('--register', type=int, choices=(3, 4, 5, 6),
                    help='Use the corresponding bundled one-row native-table patch')
parser.add_argument('--check-only', action='store_true',
                    help='Check all constrained contracts without exporting context data')
args = parser.parse_args()
if (args.json_file is None) == (args.register is None):
    parser.error('Supply either a discovery JSON file or --register, but not both.')
d = bundled_variant(args.register) if args.register is not None else json.loads(Path(args.json_file).read_text())
rows = {(q, b): (w, di, n) for q, b, w, di, n in d['rows']}
labels = sorted({q for q, b in rows}) + [254]
sites = d['source_sites']
cs = []
RAD = 12
for i, code in enumerate(d['instructions']):
    st = frame(sites[i][0])
    if code[0] == 'inc':
        _, r, n = code
        cs.append((i, None, st, canonical(frame(sites[n][0], 0, ('x', 'inc', PHYSICAL[r])))))
    elif code[0] == 'dec':
        _, r, z, p = code
        cs.append((i, (PHYSICAL[r], True), st, canonical(frame(sites[z][0]))))
        if i not in d['zero_constrained_sites']:
            cs.append((i, (PHYSICAL[r], False), st,
                       canonical(frame(sites[p][0], 1, ('x', 'dec', PHYSICAL[r])))))
    elif code[0] == 'jump':
        cs.append((i, None, st, canonical(frame(sites[code[1]][0]))))
    else:
        cs.append((i, None, st, None))
assert len(sites) == 3812 and len(cs) == 4959

contexts = collections.defaultdict(set)


def take(segs, n):
    out = []
    for x in segs:
        if x[0] == 'b':
            out.append(x[1])
        elif x[0] == 'r':
            out += [x[1]] * min(n - len(out), x[3])
            if x[2] and len(out) < n:
                break
        else:
            out.append(0)
            break
        if len(out) >= n:
            break
    return tuple(out[:n]) + (-1,) * max(0, n - len(out))


def observe(s):
    q, onl, l, r = s
    if q not in BOXSTATES and not onl and r and r[0][0] == 'b':
        contexts[q, r[0][1]].add(tuple(reversed(take(l, RAD))) + take(r, RAD + 1))


ans = validate(rows, cs, None if args.check_only else observe)
print(json.dumps({'source_sites': len(sites), 'working_states': len(rows) // 2,
                  'validation': ans, 'metadata': d.get('meta', {})}, indent=2), flush=True)
assert ans['ok']
if args.check_only:
    raise SystemExit(0)
idx = {q: i for i, q in enumerate(labels)}
states = [q for q in labels[:-1] if q not in BOXSTATES and q != 84
          and all((q, b) in contexts for b in (0, 1))]
outdir = Path('experiments')
outdir.mkdir(exist_ok=True)
with (outdir / 'contexts.dat').open('w') as f:
    print(len(labels) - 1, RAD, len(states), file=f)
    print(*[idx[q] for q in states], file=f)
    for q in labels[:-1]:
        for b in (0, 1):
            w, di, n = rows[q, b]
            print(w, int(di), idx[n], file=f)
    for q in labels[:-1]:
        for b in (0, 1):
            ts = sorted(contexts.get((q, b), []))
            print(len(ts), file=f)
            for t in ts:
                print(*t, file=f)
(outdir / 'labels.json').write_text(json.dumps(labels))
(outdir / 'variant.json').write_text(json.dumps(d))
print('exported', len(states), sum(map(len, contexts.values())), flush=True)
