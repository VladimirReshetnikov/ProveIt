#!/usr/bin/env python3
"""Independent finite audit of existing K215 left-frame proposal data.

This script imports no repository Python. It checks counts, exact source routing,
template row identities, and the 444 finite symbolic steps. It is not a substitute
for the Lean proof of frame lifting or for the full endpoint compilation.

Use --inputs for the bundled flat input directory, or --repo for a checkout.
Both modes require the exact reviewed input hashes embedded below. Only Python's
standard library is needed; no network access or proof-assistant install is used.
"""
import argparse
import collections
import hashlib
import json
import re
from pathlib import Path


REVIEW_COMMIT = "cbf94cb552a3b49509e0eee80e7455d4eb5974c6"
INPUT_SPECS = {
    "sites": {
        "filename": "sites215.json",
        "repository_path": "Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json",
        "sha256": "17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba",
        "bytes": 217322
    },
    "native": {
        "filename": "k215.native.tm",
        "repository_path": "Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.native.tm",
        "sha256": "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2",
        "bytes": 5545
    },
    "formal_table": {
        "filename": "KTable215.lean",
        "repository_path": "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KTable215.lean",
        "sha256": "429775b1774d41e94ba3b7283f7f50ea45bc13716d4ef27fccffe1f686a8d24c",
        "bytes": 11919
    },
    "decoder": {
        "filename": "K215Decoder.lean",
        "repository_path": "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/K215Decoder.lean",
        "sha256": "8663e195ec5a08d1137547eaf7332cfc32ef7c353e473437bbc3fc06cf45c373",
        "bytes": 32426
    },
    "templates": {
        "filename": "FORMAL_TEMPLATES.json",
        "repository_path": "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime/FORMAL_TEMPLATES.json",
        "sha256": "e2b8fd178afba6c85edf17eb647751d90a606541f03b01b76ec309acfdd62238",
        "bytes": 117749
    },
    "assignments": {
        "filename": "LEFT_FRAME_DISCOVERY.json",
        "repository_path": "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime/LEFT_FRAME_DISCOVERY.json",
        "sha256": "7ffd22fae7b69da1b20552129eeb0c5b7ecf82179c6664806a4bd6a6fbef364a",
        "bytes": 198086
    },
    "runtime": {
        "filename": "KRuntimeCore.lean",
        "repository_path": "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KRuntimeCore.lean",
        "sha256": "720237caea67c24657a25597b722e8add8a7fd099b33d699a0018654672d180e",
        "bytes": 22804
    },
    "simulation": {
        "filename": "KSim.lean",
        "repository_path": "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSim.lean",
        "sha256": "cb055c60ca4b41dbe36ae3356d952252661b4a15836d24b71d7aff0b579be731",
        "bytes": 16107
    },
    "endpoint": {
        "filename": "KEndpoint.lean",
        "repository_path": "Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean",
        "sha256": "04965b2e82b0f22cdbb11910c17ddf82efafe26123040d6b1b01a88707ec8175",
        "bytes": 4004
    },
    "rocq_table": {
        "filename": "Table230.v",
        "repository_path": "Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/Table230.v",
        "sha256": "497b0ad2c5829dc4712bc2aaf52c270dfc2361d5b3af80cef6b492f4293c6281",
        "bytes": 7961
    },
    "rocq_machine": {
        "filename": "TM230.v",
        "repository_path": "Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/TM230.v",
        "sha256": "0abc4b238ff45222480f6a6e2ec96350fd3e04bd8c07ee88302b7cce7b029c2d",
        "bytes": 4979
    }
}


def require(condition, description):
    if not condition:
        raise ValueError(description)


def tup(x):
    return tuple(map(tup, x)) if isinstance(x, list) else x


def bit(b):
    return ('b', int(b))


def scan(word):
    k = 0
    for b in word:
        k = 0 if b == '1' else k + 1
        if k >= 8:
            return None
    return k


def strip(word, b, k):
    while k and word:
        k -= int(word[-1] == b)
        word = word[:-1]
    return word


def inc(word):
    # Fixed-width binary successor, as in RegisterPath.incRev/incPath.
    bs = list(word)
    i = len(bs) - 1
    while i >= 0 and bs[i] == '1':
        bs[i] = '0'
        i -= 1
    if i >= 0:
        bs[i] = '1'
    return ''.join(bs), i < 0


def normal(segments):
    out = []
    for x in segments:
        if x[0] == 'b':
            x = ('r', x[1], 0, 1)
        if x[0] == 'r':
            if x[2:] == (0, 0):
                continue
            if out and out[-1][0] == 'r' and out[-1][1] == x[1]:
                y = out.pop()
                x = ('r', x[1], x[2] + y[2], x[3] + y[3])
        out.append(x)
    return tuple(out)


def oracle(q, branch, x):
    skips = (51, 36, 25, 48, 32, 33, 22, 55, 60)
    if x[1] == 'none':
        if q not in skips:
            return None
        r = skips.index(q)
        return (1 if r == 0 else 3, ('x', 'mark', r), False)
    if x[1] == 'mark':
        r = x[2]
        if r >= 9:
            return None
        if q == 64:
            return (40, ('x', 'inc', r), False)
        if q == 0 and branch is not None and branch[0] == r:
            return (97, ('x', 'none', 0), False) if branch[1] else (40, ('x', 'dec', r), True)
    return None


def sstep(table, branch, s):
    q, on_left, l, r = s
    if on_left:
        if not l:
            return ((q, False, (), (bit(0),) + r), False)
        x, tail = l[0], l[1:]
        if x[0] == 'b':
            return ((q, False, tail, (x,) + r), False)
        if x[0] == 'x':
            return None
        _, b, a, c = x
        row = table.get((q, b))
        if row is not None and not row[1] and row[2] == q:
            return ((q, True, tail, (('r', row[0], a, c),) + r), False)
        if c:
            return ((q, True, (bit(b), ('r', b, a, c - 1)) + tail, r), False)
        if not a:
            return ((q, True, tail, r), False)
        return None
    if not r:
        return None
    x, tail = r[0], r[1:]
    if x[0] == 'b':
        row = table.get((q, x[1]))
        if row is None:
            return None
        w, right, q2 = row
        if right:
            return ((q2, False, (bit(w),) + l, tail), True)
        return ((q2, True, l, (bit(w),) + tail), True)
    if x[0] == 'r':
        _, b, a, c = x
        row = table.get((q, b))
        if row is not None and row[1] and row[2] == q:
            return ((q, False, (('r', row[0], a, c),) + l, tail), False)
        if c:
            return ((q, False, l, (bit(b), ('r', b, a, c - 1)) + tail), False)
        if not a:
            return ((q, False, l, tail), False)
        return None
    if tail:
        return None
    o = oracle(q, branch, x)
    if o is not None:
        q2, x2, extra = o
        return ((q2, True, (bit(1),) + l if extra else l, (x2,)), False)
    row = table.get((q, 0))
    if row is not None and row[0] == 0 and not row[1]:
        return ((row[2], True, l, (x,)), True)
    return None


def parse_table(text):
    body = text.split('def table215 : List (Row × Row) := [', 1)[1].split(']\n', 1)[0]
    rows = re.findall(r'none|some \((?:true|false), (?:true|false), \d+\)', body)
    require(len(rows) % 2 == 0, 'unaligned formal rows')
    out = {}
    for i, row in enumerate(rows):
        if row != 'none':
            w, d, z = re.fullmatch(r'some \((true|false), (true|false), (\d+)\)', row).groups()
            out[i // 2, i % 2] = (int(w == 'true'), d == 'true', int(z))
    return out


def parse_rocq_table(table_text, machine_text):
    """Read the maintained Rocq table and its explicit disabled-state guard."""
    body = table_text.split('Definition table230 :', 1)[1].split(':= [', 1)[1].split('].', 1)[0]
    rows = re.findall(r'\((true|false), (L|R), (\d+), (true|false), (L|R), (\d+)\)', body)
    require(len(rows) == 230, 'wrong Rocq table length')
    guard = machine_text.split('Definition tmn ', 1)[1].split('then None else', 1)[0]
    disabled = set(map(int, re.findall(r'Nat.eqb q (\d+)', guard)))
    require(len(disabled) == 15, 'wrong Rocq disabled-state count')
    table = {}
    for q, row in enumerate(rows):
        if q in disabled:
            continue
        for b in (0, 1):
            w, d, z = row[3*b:3*b+3]
            table[q, b] = (int(w == 'true'), d == 'R', int(z))
    return table, sorted(disabled)


def parse_decoder(text):
    body = text.split('def sourceNodes :', 1)[1].split('#[', 1)[1].split(']', 1)[0]
    nodes = [(k, int(a), int(b)) for k, a, b in re.findall(r'\.(leaf|fork) (\d+) (\d+)', body)]
    roles = []
    body = text.split('def roles : Array Role := #[', 1)[1].split('\n\n', 1)[0]
    for line in body.splitlines():
        if not line.strip() or line.strip() == ']':
            continue
        m = re.match(r'\s*⟨(\d+), (\d+), \[([^]]*)\], (.*)⟩[,\]]*', line)
        require(m is not None, 'unparsed decoder role')
        node, q, ctx, es = m.groups()
        edges = []
        for e in re.finditer(r'\(\.internal (\d+) (\d+)\)|\(\.primitive (\d+) ⟨(true|false), (\(?-?1\)?), (\d+)⟩\)', es):
            a, b, n, w, dr, z = e.groups()
            if a is not None:
                edges.append(('internal', int(a), int(b)))
            else:
                edges.append(('primitive', int(n), (int(w == 'true'), int(dr.strip('()')) == 1, int(z))))
        require(len(edges) == 2, 'role must have two edges')
        roles.append((int(node), int(q), tuple(int(b.strip() == 'true') for b in ctx.split(',') if b.strip()), edges))
    return nodes, roles


def main():
    p = argparse.ArgumentParser()
    location = p.add_mutually_exclusive_group(required=True)
    location.add_argument('--inputs', type=Path, help='Flat bundled input directory')
    location.add_argument('--repo', type=Path, help='ProveIt checkout with the reviewed source bytes')
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    paths = {
        key: (a.inputs / spec['filename'] if a.inputs is not None
              else a.repo / spec['repository_path'])
        for key, spec in INPUT_SPECS.items()
    }
    data = {k: p.read_bytes() for k, p in paths.items()}
    for key, raw in data.items():
        spec = INPUT_SPECS[key]
        require(len(raw) == spec['bytes'], f'wrong input byte count: {key}')
        require(hashlib.sha256(raw).hexdigest() == spec['sha256'], f'wrong pinned input hash: {key}')
    sites = json.loads(data['sites'])
    td = json.loads(data['templates'])['templates_data']
    assignments = json.loads(data['assignments'])
    table = parse_table(data['formal_table'].decode())
    rename = lambda q: {301: 102, 302: 120, 254: 230}.get(q, q)
    native = {}
    for line in data['native'].decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, q2 = line.split()
        native[rename(int(q)), int(b)] = (int(w), d == 'R', rename(int(q2)))
    require(table == native and len(table) == 430, 'literal native/formal tables disagree')
    rocq_table, rocq_disabled = parse_rocq_table(data['rocq_table'].decode(), data['rocq_machine'].decode())
    require(rocq_table == table, 'maintained Rocq and Lean tables disagree')
    nodes, roles = parse_decoder(data['decoder'].decode())
    ops = {0: 'CI', 1: 'CD', 2: 'CB', 3: 'CC', 4: 'CH'}
    expanded = []
    def expand(n, pc):
        kind, x, y = nodes[n]
        if kind == 'leaf':
            expanded.append([pc, ops[x], None if x == 4 else y])
        else:
            require(x < n and y < n, 'DAG must decrease')
            expand(x, pc + '0')
            expand(y, pc + '1')
    expand(201, '')
    # CH's third field is retained as published; it has no semantic argument.
    require(len(expanded) == len(sites), 'wrong source expansion size')
    require(all(x[:2] == y[:2] and (x[1] == 'CH' or x[2] == y[2]) for x, y in zip(expanded, sites)), 'source expansion differs')
    ports = {}
    for pc, op, arg in sites:
        rid, node, hist = 0, 201, (1,)
        for b in map(int, pc[:-1]):
            n, q, ctx, es = roles[rid]
            require(n == node and ctx == hist[-2:] and nodes[n][0] == 'fork', 'bad routed prefix')
            edge = es[b]
            require(edge[0] == 'internal', 'premature primitive')
            rid, node, hist = edge[1], nodes[n][1 + b], hist + (b,)
        n, q, ctx, es = roles[rid]
        b = int(pc[-1])
        edge = es[b]
        require(n == node and ctx == hist[-2:] and edge[0] == 'primitive', 'bad routed primitive')
        require(nodes[n][1 + b] == edge[1], 'primitive child mismatch')
        kind, code, reg = nodes[edge[1]]
        require(kind == 'leaf' and ops[code] == op and (op == 'CH' or reg == arg), 'leaf instruction mismatch')
        require(table[q, b] == edge[2], 'primitive table row mismatch')
        ports[pc] = q
    counters = collections.Counter(op for _, op, _ in sites)
    require(counters == {'CI': 1900, 'CD': 1425, 'CB': 98, 'CC': 1327, 'CH': 1}, 'unexpected leaf census')
    trace_steps = 0
    for i, t in enumerate(td):
        require(t['id'] == i, 'nonsequential template id')
        key = t['key']
        _, q, suffix, op, arg, pos, end, delta, overflow, diff = key
        require(op in ('CC', 'CB') and not pos and delta == overflow == 0 and diff == len(suffix) - len(end), 'unsupported key')
        expected = (q, False, tuple(bit(int(b)) for b in reversed(suffix[:-1])), (bit(int(suffix[-1])), ('r', 0, 1, 16), bit(1), ('x', 'none', 0)))
        require(tup(t['start']) == expected, 'wrong template start')
        s = expected
        require(len(t['trace']) == t['steps'], 'wrong trace length')
        for j, edge in enumerate(t['trace']):
            require(tup(edge['before']) == s, 'noncontiguous trace')
            require(not (s[1] and not s[2]), 'unsafe frame read')
            got = sstep(table, None, s)
            require(got == (tup(edge['after']), edge['moved']), f'false symbolic step {i}/{j}')
            s = got[0]
            trace_steps += 1
        require(s == tup(t['pre_home']) and s[:3] == (2, True, ()), 'wrong Home boundary')
        target = tuple(bit(int(b)) for b in end) + (('r', 0, 1, 16 + diff), bit(1), ('x', 'none', 0))
        require(normal(s[3]) == normal(target), 'wrong symbolic right endpoint')
    uses = collections.Counter()
    assigned = set()
    ends_zero = 0
    use_ops = collections.Counter()
    for row in assignments['guard_records']:
        i, cut, t_id = row['site'], row['cut'], row['template']
        require(i not in assigned, 'duplicate assigned site')
        assigned.add(i)
        pc, op, arg = sites[i]
        prefix, suffix = pc[:cut], pc[cut:]
        require(0 < cut < len(pc), 'empty prefix or suffix')
        _, q, actual_suffix, actual_op, actual_arg, _, end, _, _, diff = td[t_id]['key']
        require((q, suffix, op, arg) == (ports[pc], actual_suffix, actual_op, actual_arg), 'template binding mismatch')
        b = '1' if op == 'CC' else '0'
        require(suffix.count(b) >= arg, 'path stripping crosses prefix')
        stripped = strip(suffix, b, arg)
        if op == 'CC':
            require(end == stripped, 'incorrect continue suffix')
            successor = strip(pc, b, arg)
        else:
            after, carry = inc(stripped)
            require(not carry and after == end, 'break carry crosses prefix')
            successor, full_carry = inc(strip(pc, b, arg))
            require(not full_carry, 'unexpected full carry')
        require(successor == prefix + end, 'whole path effect mismatch')
        require(diff == len(pc) - len(successor), 'gap correction mismatch')
        require(len(pc) <= 48 and scan(prefix[::-1]) == row['home_scan_bound'], 'bad Home scan or gap premise')
        uses[t_id] += 1
        use_ops[op] += 1
        ends_zero += prefix.endswith('0')
    literal = set()
    for row in assignments['literal_controls']:
        i = row['site']
        require(i not in assigned and i not in literal, 'overlapping fallback')
        require(sites[i] == [row['pc'], row['op'], row['arg']], 'wrong fallback')
        literal.add(i)
    control = {i for i, (_, op, _) in enumerate(sites) if op in ('CB', 'CC')}
    require(assigned | literal == control, 'incomplete control coverage')
    require(len(assigned) == 1422 and len(literal) == 3 and len(uses) == len(td) == 35, 'wrong compression count')
    original = counters['CI'] + 2 * counters['CD'] + len(control) + counters['CH']
    expensive = counters['CI'] + 2 * counters['CD'] + len(literal) + len(td) + counters['CH']
    require((original, expensive) == (6176, 4789), 'wrong outcome census')
    # A concrete counterexample to dropping the safe-left guard.
    s = (0, True, (), (bit(1),))
    frame = (bit(1),)
    no_frame = sstep(table, None, s)[0]
    framed = sstep(table, None, (s[0], s[1], s[2] + frame, s[3]))[0]
    require(framed != (no_frame[0], no_frame[1], no_frame[2] + frame, no_frame[3]), 'guard counterexample disappeared')
    result = {
        'status': 'PASS',
        'scope': 'Independent finite source/routing/template audit; no Lean/Rocq kernel or endpoint claim.',
        'repository': 'https://github.com/VladimirReshetnikov/ProveIt',
        'review_commit': REVIEW_COMMIT,
        'input_mode': 'bundled_flat_inputs' if a.inputs is not None else 'repository_checkout',
        'leaf_count': len(sites), 'leaf_counts': dict(counters),
        'source_nodes': len(nodes), 'decoder_roles': len(roles), 'table_rows': len(table),
        'rocq_table_matches_lean': True, 'rocq_disabled_states': rocq_disabled,
        'template_count': len(td), 'symbolic_step_count': trace_steps,
        'max_template_steps': max(t['steps'] for t in td),
        'control_uses': len(assigned), 'control_use_operations': dict(use_ops),
        'prefixes_ending_zero': ends_zero, 'literal_controls': assignments['literal_controls'],
        'template_multiplicities': dict(sorted(uses.items())),
        'original_guarded_outcomes': original, 'candidate_expensive_obligations': expensive,
        'candidate_obligations_saved': original - expensive,
        'saved_fraction': (original - expensive) / original,
        'safe_left_guard_counterexample_checked': True,
        'sources': {k: {'path': INPUT_SPECS[k]['repository_path'],
                        'bundle_file': INPUT_SPECS[k]['filename'],
                        'sha256': hashlib.sha256(v).hexdigest(), 'bytes': len(v)}
                    for k, v in data.items()},
    }
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('sources', 'template_multiplicities')}, indent=2))


if __name__ == '__main__':
    main()
