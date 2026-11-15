#!/usr/bin/env python3
"""Independently check the finite PA194 -> PA194SEL simulation certificate.

No builder import and no named arithmetic-box lemma is used. The complete
unbounded iPRA induction that consumes this certificate is in the report.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    rows = {}
    for ln in path.read_text().splitlines():
        if not ln.strip() or ln.lstrip().startswith('#'):
            continue
        q, b, w, d, n = ln.split()
        q, b, w, n = map(int, (q, b, w, n))
        require((q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Bad transition')
        rows[q, b] = (w, 1 if d == 'R' else -1, n)
    states = {q for q, b in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete transition table')
    terminal = {n for w, d, n in rows.values()} - states
    require(len(terminal) == 1, 'Expected exactly one terminal halt label')
    return rows, states, terminal.pop()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rho(q):
    return {38: 12, 124: 127}.get(q, q)


def literal_run(rows, length):
    q, h, tape = 74, 0, set()
    visits = {12: 0, 38: 0, 124: 0, 127: 0}
    for t in range(length):
        require(q != 254, 'Unexpected early halt')
        b = int(h in tape)
        if q in visits and b == 0:
            visits[q] += 1
        w, d, q = rows[q, b]
        (tape.add if w else tape.discard)(h)
        h += d
    return q, h, tape, visits


def check(output):
    primary_path = ROOT / 'inputs/primary.tm'
    require(sha(primary_path) == '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f', 'Pinned dense input hash differs')
    old_path = ROOT / 'inputs/primary.native.tm'
    require(sha(old_path) == 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54', 'Pinned native input hash differs')
    old, states, halt = load(old_path)
    dense0, states0, halt0 = load(primary_path)
    old_labels = json.loads((ROOT / 'inputs/primary.labels.json').read_text())
    require(states0 == set(range(194)) and halt0 == 194, 'Bad primary numbering')
    require(len(set(old_labels)) == 195 and old_labels[0] == 74 and old_labels[-1] == 254, 'Bad primary labels')
    require({(old_labels[q], b): (w, d, old_labels[n]) for (q, b), (w, d, n) in dense0.items()} == old, 'Primary conjugacy fails')
    new_path = ROOT / 'machine/pa194sel.native.tm'
    new, ns, nh = load(new_path)
    require(ns == states and len(states) == 194 and halt == nh == 254, 'State count differs')
    expected = {
        (12, 0): ((0, 1, 19), (0, -1, 38)),
        (38, 0): ((0, 1, 28), (0, 1, 98)),
        (38, 1): ((1, 1, 20), (1, 1, 19)),
        (312, 1): ((1, 1, 38), (1, 1, 12)),
        (104, 1): ((1, 1, 124), (1, 1, 127)),
        (124, 0): ((0, 1, 62), (0, 1, 8)),
        (124, 1): ((1, 1, 138), (1, 1, 59)),
        (127, 0): ((0, 1, 14), (0, -1, 124)),
    }
    require({key: (old[key], new[key]) for key in old if old[key] != new[key]} == expected, 'Unexpected native row delta')
    histories = {12: 0, 38: 1, 127: 0, 124: 1}
    incoming = {}
    for target, hist in histories.items():
        edges = [(q, b, w, d) for (q, b), (w, d, n) in old.items() if n == target]
        require(edges and all((w, d) == (hist, 1) for q, b, w, d in edges), 'Entry-history premise fails')
        incoming[target] = edges
    require(74 not in histories and rho(254) == 254, 'Start or halt is exceptional')
    ordinary = 0
    for (q, b), (w, d, n) in old.items():
        if q not in histories:
            require(new[rho(q), b] == (w, d, rho(n)), 'Ordinary step fails')
            ordinary += 1
    require(ordinary == 380, 'Wrong ordinary-case count')
    cases = []
    for oldq, hist in histories.items():
        for bit in (0, 1):
            cells = {-1: hist, 0: bit}
            w, d, n = old[oldq, bit]
            goal = rho(n), d, {-1: hist, 0: w}
            q, pos = rho(oldq), 0
            trace = [dict(q=q, head=pos, cells=dict(cells))]
            for duration in range(1, 4):
                require(pos in cells and q != 254, 'Exterior read or premature halt')
                w, d, q = new[q, cells[pos]]
                cells[pos] = w; pos += d
                trace.append(dict(q=q, head=pos, cells=dict(cells)))
                if (q, pos, cells) == goal:
                    break
            else:
                raise ValueError('Exact local identity failed')
            require(duration == (3 if bit == 0 else 1), 'Wrong local duration')
            cases.append(dict(old_state=oldq, history=hist, read=bit, duration=duration, trace=trace))
    dense, ds, dh = load(ROOT / 'machine/pa194sel.tm')
    labels = json.loads((ROOT / 'machine/pa194sel.labels.json').read_text())
    require(ds == set(range(194)) and dh == 194, 'Bad dense output')
    require(len(set(labels)) == 195 and labels[0] == 74 and labels[-1] == 254, 'Bad output labels')
    require({(labels[q], b): (w, d, labels[n]) for (q, b), (w, d, n) in dense.items()} == new, 'Output conjugacy fails')
    reached, work = {0}, [0]
    for q in work:
        for bit in (0, 1):
            n = dense[q, bit][2]
            if n != 194 and n not in reached:
                reached.add(n); work.append(n)
    require(reached == ds, 'Unreachable working state')
    before = literal_run(old, 58154)
    startup_steps = 58154 + 2 * sum(before[3].values())
    after = literal_run(new, startup_steps)
    require(startup_steps == 58208 and before[:3] == after[:3], 'Whole-tape startup mismatch')
    require(before[0:2] == (84, -2), 'Wrong source seed checkpoint')
    result = dict(status='PASS', working_states=194, transition_rows=388,
                  dense_sha256=sha(ROOT / 'machine/pa194sel.tm'), native_sha256=sha(new_path),
                  changed_native_rows=8, ordinary_cases=ordinary, local_cases=cases,
                  incoming_history_edges=incoming, arbitrary_exterior_tape_untouched=True,
                  all_working_states_graph_reachable=True, primary_startup_steps=58154,
                  new_startup_steps=startup_steps, complete_seed_tape_equal=True,
                  source_seed=dict(native_state=after[0], head=after[1], one_cells=sorted(after[2])),
                  primary_startup_exceptional_read0_counts=before[3],
                  bounds=dict(old_halts_by_t_implies_new_halts_by='3*t', new_halts_by_T_implies_old_halts_by='T'),
                  kernel_checked=False,
                  scope='Finite certificate consumed by the explicit quantifier-free induction in the report; direct relative iPRA halting equivalence to the primary, with the absolute calibration kept separate')
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('local_cases', 'source_seed')}, indent=2))
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT / 'verification/receipt.json')
    check(ap.parse_args().output)
