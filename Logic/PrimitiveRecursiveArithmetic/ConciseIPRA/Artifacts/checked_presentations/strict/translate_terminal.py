"""Untrusted translator from zero-as-1 supply certificates to terminal proofs.

Only the measured checker decides acceptance. This utility reconstructs a
successful reference trace, removes computation-supply cuts, renames numerical
parameters, and inserts explicit terminal packets. It does not run while the
checker validates a proof. The supported trace fragment requires computation
supplies to be closed at the previous floor, as canonical certificates are.
"""
import copy
import json
from pathlib import Path


def opening(a, k, t=None, d=0):
    if type(a) is list:
        return [opening(b, k, t, d + 5 - len(a)) for b in a]
    if type(a) is not int:
        raise ValueError('non-integer scalar or absent image')
    if k <= a < d:
        return a or 1
    return d % 2 and opening(t, k, d=3)


def computation(s, u, t, k):
    return [[s and [s], u, t], opening(t, k, [s, u, t], 3) if s else u]


def rename(a, env):
    if type(a) is list:
        return [rename(b, env) for b in a]
    if type(a) is int and a < 0:
        return env[a]
    return a


def trace(certificate):
    pending = copy.deepcopy(certificate[:-1])
    count = 0

    def parse(g, a, k):
        nonlocal count
        count += 1
        if count > 100000:
            raise ValueError('trace budget')
        normalized = opening(a, k)
        for value, origin in g:
            if normalized == value:
                return {'kind': 'hyp', 'a': a, 'k': k, 'origin': origin}
        m, s, u, t = packet = pending.pop()
        major = parse(g, m, k)
        if m:
            raw = m * 3
            kind = 'major'
        elif u:
            raw = computation(s, u, t, k)
            kind = 'compute'
        else:
            a = opening(a[0], k, t, 2)
            raw = a
            kind = 'intro'
        fresh = k - 1
        mode = bool(m or len(a) % 2 == u)
        h = opening(raw, fresh, int(mode) * fresh)
        if (m, a) == (s and [s, u] or [t] * 3, opening(t, fresh, u)):
            endpoint = opening(t, fresh, s)
        else:
            endpoint = a
        child_a = opening(endpoint, fresh, [fresh])
        origin = {'kind': 'compute', 'packet': packet} if kind == 'compute' else {'kind': 'assumption'}
        if kind == 'compute':
            if opening(raw, k) != h:
                raise ValueError('noncanonical computation supply has a fresh hole')
        node = {'kind': kind, 'a': normalized, 'k': k, 'packet': packet,
                'major': major, 'fresh': fresh, 'h': h}
        node['child'] = parse(g + [(h, origin)], child_a, fresh)
        return node

    proof = parse([(0, {'kind': 'neutral'})], certificate[-1], 0)
    return proof, {'source_calls': count, 'unused_source_prefix': len(pending)}


def convert(certificate):
    proof, stats = trace(certificate)
    output = []
    dummy = [0, 0, 0, 0]
    stats.update({'skipped_supplies': 0, 'hypothesis_terminals': 0, 'computation_terminals': 0})

    def emit(node, g, a, k, env):
        norm = opening(a, k)
        if norm in g:
            output.append(copy.deepcopy(dummy))
            stats['hypothesis_terminals'] += 1
            return
        kind = node['kind']
        if kind == 'hyp':
            origin = node['origin']
            if origin['kind'] != 'compute':
                raise ValueError('lost non-computation assumption')
            packet = rename(origin['packet'], env)
            _, s, u, t = packet
            if opening(computation(s, u, t, k), k) != norm:
                raise ValueError('supplied computation fails projected match')
            output.append(packet)
            stats['computation_terminals'] += 1
            return
        if kind == 'compute':
            stats['skipped_supplies'] += 1
            extended = dict(env)
            extended[node['fresh']] = 1
            if opening(rename(node['child']['a'], extended), k) != norm:
                raise ValueError('computation supply changes the canonical goal')
            emit(node['child'], g, a, k, extended)
            return
        packet = rename(node['packet'], env)
        m, s, u, t = packet
        if kind == 'intro' and u == 0:
            packet[2] = u = 2
        output.append(copy.deepcopy(packet))
        # The candidate can close early at the generated computation equation.
        if opening(computation(s, u, t, k), k) == norm:
            stats['computation_terminals'] += 1
            return
        emit(node['major'], g, m, k, env)
        if m:
            raw = m * 3
        else:
            a = opening(a[0], k, t, 2)
            raw = a
        fresh = k - 1
        mode = bool(m or len(a) == u == 2)
        h = opening(raw, fresh, int(mode) * fresh)
        if (m, a) == (s and [s, u] or [t] * 3, opening(t, fresh, u)):
            endpoint = opening(t, fresh, s)
        else:
            endpoint = a
        child_a = opening(endpoint, fresh, [fresh])
        extended = dict(env)
        extended[node['fresh']] = fresh
        old_child = opening(rename(node['child']['a'], extended), fresh)
        if old_child != opening(child_a, fresh):
            raise ValueError('renamed continuation differs')
        emit(node['child'], g + [h], child_a, fresh, extended)

    emit(proof, [0], certificate[-1], 0, {})
    stats['new_packets'] = len(output)
    return list(reversed(output)) + [copy.deepcopy(certificate[-1])], stats


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('target', type=Path)
    args = parser.parse_args()
    result, statistics = convert(json.loads(args.source.read_text()))
    args.target.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print(json.dumps(statistics, sort_keys=True))
