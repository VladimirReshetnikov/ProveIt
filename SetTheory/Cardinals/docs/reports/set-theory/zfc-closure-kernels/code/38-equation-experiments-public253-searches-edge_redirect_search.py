"""Predecessor-sensitive, whole-window certificates for deleting a TM state.

The abstract reachable windows overapproximate the original blank execution.
For each edge from a retained state into removed state p, choose its own
replacement q. After the unchanged write and move of that edge, compare the
original from p and the candidate from q until they reach exactly the same
retained control, relative head and full known window. Neither run may read
outside that initial window. Candidate prefixes may not enter p. This makes
different edge choices independent and gives a sound positive-progress block
simulation: the incoming transition itself supplies one step on each side.
For a removed initial state the blank-window block must make positive progress
on both sides. A successful certificate can then be checked against the whole
candidate table. A failure of these bounded sufficient checks is no lower bound.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from collections import defaultdict
from pathlib import Path
from upstream_audit_tm import Machine, Edge, parse_table, window_reachable


def edge_windows(machine: Machine, windows: dict[int, list[int]], radius: int):
    full = (1 << (2 * radius + 1)) - 1
    out = defaultdict(set)
    for q, patterns in windows.items():
        if q == machine.halt:
            continue
        for pattern in patterns:
            b = (pattern >> radius) & 1
            e = machine.rows[q, b]
            written = (pattern & ~(1 << radius)) | (e.write << radius)
            if e.move == 1:
                shifted, unknown = written >> 1, 1 << (2 * radius)
            else:
                shifted, unknown = (written << 1) & full, 1
            out[q, b].update((shifted, shifted | unknown))
    return {edge: sorted(ps) for edge, ps in out.items()}


def local_trace(machine, start, pattern, radius, bound, forbidden=None):
    head, q = 0, start
    out = [(q, head, pattern)]
    for _ in range(bound):
        if q == machine.halt or not -radius <= head <= radius:
            break
        pos = head + radius
        e = machine.rows[q, (pattern >> pos) & 1]
        if e.target == forbidden:
            break
        pattern = (pattern & ~(1 << pos)) | (e.write << pos)
        head += e.move
        q = e.target
        out.append((q, head, pattern))
    return out


def original_targets(machine, p, pattern, radius, bound):
    targets = {}
    for i, (q, head, tape) in enumerate(local_trace(machine, p, pattern, radius, bound)):
        if q != p:
            key = ('halt',) if q == machine.halt else (q, head, tape)
            targets.setdefault(key, i)
    return targets


def replacement_certificate(machine, p, q, patterns, radius, bound, originals,
                            start_case=False):
    cert = []
    for pattern in patterns:
        target = originals[pattern]
        trace = local_trace(machine, q, pattern, radius, bound, forbidden=p)
        for j, (state, head, tape) in enumerate(trace):
            if start_case and j == 0:
                continue
            key = ('halt',) if state == machine.halt else (state, head, tape)
            if key in target:
                cert.append([pattern, target[key], j])
                break
        else:
            return None
    return cert


def search(machine, radius=5, bound=64):
    t0 = time.monotonic()
    windows = window_reachable(machine, radius)
    ew = edge_windows(machine, windows, radius)
    all_results, candidates, checks = [], [], 0
    for p in machine.states:
        incoming = [key for key, e in machine.rows.items() if e.target == p and key[0] != p]
        if machine.start == p:
            incoming.insert(0, ('start', 0))
        # Fail fast at large incoming contexts; all proposals still use every
        # edge, if its earlier edges admit a replacement.
        incoming.sort(key=lambda key: -len(ew.get(key, [0])))
        originals = {w: original_targets(machine, p, w, radius, bound)
                     for w in windows[p]}
        edge_records, complete = [], True
        for edge in incoming:
            patterns = [0] if edge[0] == 'start' else ew[edge]
            accepted = []
            for q in machine.states:
                if q == p:
                    continue
                checks += 1
                cert = replacement_certificate(machine, p, q, patterns, radius,
                                               bound, originals, edge[0] == 'start')
                if cert is not None:
                    accepted.append({'replacement': q, 'certificate': cert})
            edge_records.append({'edge': list(edge), 'windows': len(patterns),
                                 'replacements': accepted})
            if not accepted:
                complete = False
                break
        rec = {'deleted': p, 'incoming_edges': len(incoming),
               'checked_edges': edge_records, 'all_edges_certified': complete}
        all_results.append(rec)
        if complete:
            candidates.append(rec)
    return {'method': __doc__, 'radius': radius, 'bound': bound,
            'abstract_configurations': sum(map(len, windows.values())),
            'edge_replacement_attempts': checks, 'states': all_results,
            'candidates': candidates, 'elapsed_seconds': time.monotonic()-t0}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table', type=Path)
    ap.add_argument('--radius', type=int, default=5)
    ap.add_argument('--bound', type=int, default=64)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    data = args.table.read_bytes()
    m = parse_table(data.decode())
    result = search(m, args.radius, args.bound)
    result['input'] = {'sha256': hashlib.sha256(data).hexdigest(),
                       'working_states': len(m.states), 'start': m.start, 'halt': m.halt}
    result['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('method','states','candidates')}))
    print('candidates:', [x['deleted'] for x in result['candidates']])


if __name__ == '__main__':
    main()
