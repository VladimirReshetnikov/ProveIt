"""Untrusted, checked trace translators for the supplied positive fixtures.

They instrument the old complete programs. Every old hypothesis return gets
one harmless packet, and the global AST profile also checks a neutral major
at introductions. Canonical fixed-point conditions are checked explicitly.
These producers are NOT imported by any trusted acceptance program.
"""
import json
import sys


def stream(records, neutral_major=False):
    if not records:
        raise ValueError('missing goal')
    goal, *packets = records
    incoming = iter(packets)
    outgoing = []
    floor = 0
    stats = {'entries': 0, 'hypotheses': 0, 'computations': 0,
             'logical_steps': 0, 'inferred_eliminations': 0,
             'fixed_point_checks': 0, 'neutral_major_packets': 0}

    def opening(a, t=0j, d=0):
        try:
            return [opening(b, t, d + 5 - len(a)) for b in a]
        except:
            return a if floor <= a < d else d % 2 and opening(t, d=3)

    def proof(a, *context):
        nonlocal floor
        while True:
            stats['entries'] += 1
            projected = opening(a)
            if opening(projected) != projected:
                raise ValueError('opener idempotence failed')
            if projected != a:
                raise ValueError('source trace needs canonicalization')
            stats['fixed_point_checks'] += 1
            if projected in context:
                outgoing.append([0, 0, 0])
                stats['hypotheses'] += 1
                return
            s, u, t = record = next(incoming)
            outgoing.append(record)
            computed = [[s and [s], u, t], opening(t, record, 3) if s else u]
            if a == computed:
                stats['computations'] += 1
                return
            if opening(t, u) == a:
                a = opening(t, s)
                s = record[:2] if s else [t] * 3
                stats['inferred_eliminations'] += 1
            if s:
                proof(s, *context)
                hypothesis = s * 3
            else:
                if neutral_major:
                    outgoing.append([0, 0, 0])
                    stats['neutral_major_packets'] += 1
                a = opening(*a, t, 2)
                hypothesis = a
            floor -= 1
            context += (opening(hypothesis, (s or len(a) == 2) and floor),)
            a = opening(a, [floor])
            stats['logical_steps'] += 1

    proof(goal)
    return [goal] + outgoing, stats


def array(certificate):
    incoming = list(certificate)
    header = incoming.pop()
    if len(header) != 2 or type(header[1]) is not int or header[1] != 0:
        raise ValueError('expected the inherited [goal,0] header')
    outgoing = []
    stats = {'entries': 0, 'hypotheses': 0, 'computations': 0,
             'logical_steps': 0, 'neutral_majors': 0,
             'fixed_point_checks': 0}

    def proof(context, a, floor):
        stats['entries'] += 1

        def opening(a, t=proof, d=0):
            if a * 0 != 0:
                return [opening(b, t, d + 5 - len(a)) for b in a]
            return a if floor <= a < d else d % 2 * opening(t, d=3)

        projected = opening(a)
        if projected != a or opening(projected) != projected:
            raise ValueError('eager no-image opening was not the identity')
        stats['fixed_point_checks'] += 1
        if projected in context:
            outgoing.append([0, 0, 0, 0])
            stats['hypotheses'] += 1
            if a == []:
                stats['neutral_majors'] += 1
            return True
        m, s, u, t = packet = incoming.pop()
        outgoing.append(packet)
        computed = [[s and [s], u, t], opening(t, [s, u, t], 3) if s else u]
        if a == computed:
            stats['computations'] += 1
            return [True]
        major = proof(context, m, floor)
        h = major and m * 3
        if not h:
            a = opening(*a, t, 2)
            h = a
        if type(a) is not list or not a:
            raise ValueError('canonical selector needs a nonempty formula')
        mode = bool(m or 3 % len(a))
        floor -= 1
        new_context = context + [opening(h, mode * floor)]
        # The original Python expression evaluates this tuple eagerly.
        target_options = (a, opening(t, s))
        selected = (m, a) == (s and [s, u] or [t] * 3, opening(t, u))
        new_goal = opening(target_options[selected], [floor])
        stats['logical_steps'] += 1
        return [proof(new_context, new_goal, floor)]

    proof([[]], *header)
    return list(reversed(outgoing)) + [header], stats


def jsonl(records):
    return ''.join(json.dumps(row, separators=(',', ':')) + '\n' for row in records).encode()


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in ('tokens', 'ast', 'bytes'):
        raise SystemExit('usage: python3 tests/translate.py tokens|ast|bytes < old-certificate')
    mode = sys.argv[1]
    if mode == 'bytes':
        converted, _ = array(json.load(sys.stdin))
        print(json.dumps(converted, separators=(',', ':')))
    else:
        converted, _ = stream([json.loads(s) for s in sys.stdin if s.strip()], mode == 'ast')
        sys.stdout.buffer.write(jsonl(converted))


if __name__ == '__main__':
    main()
