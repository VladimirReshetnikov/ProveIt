"""Checked proof transformations for the goal-directed packet protocol.

The source is the explicit four-pattern recursive-formula Horn checker,
frozen in reference/control_recursive.py. Source contexts include the
initial universal-reflexivity clause; packet context indices omit it.
"""
import copy
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


explicit = load('explicit_horn', ROOT / 'reference' / 'control_recursive.py')
packet = load('packet_horn', ROOT / 'checker.py')
INITIAL = [([], [1, 1])]


def verify_packets(certificate):
    packet.require(type(certificate) is list and bool(certificate))
    packet.packets = copy.deepcopy(certificate)
    goal = packet.packets.pop()
    packet.check(goal)
    packet.require(not packet.packets)
    return goal


def events(proof, context):
    """The sequence of packets in consumption order, for a valid source proof."""
    goal = explicit.derive(proof, context)
    if goal[0] == goal[1]:
        return []
    fresh = -len(context)
    match proof:
        case ['u', index, witness, premises]:
            return [[index - 1, witness]] + [event for p in premises for event in events(p, context)]
        case ['x', major, minor]:
            left = explicit.derive(major, context)
            right = explicit.derive(minor, context)
            return [[left, right]] + events(major, context) + events(minor, context)
        case ['e', goal, major, branch]:
            source = explicit.derive(major, context)
            body = explicit.opening(source[1], fresh, 1)
            clause = ([explicit.opening(body, 0)], body)
            return [[source, 0]] + events(major, context) + events(branch, context + [clause])
        case ['i', goal, witness, branch]:
            body = explicit.opening(goal[1], witness, 1)
            eta = fresh if goal[1][0] != 'd' and witness == 0 else 0
            clause = ([], explicit.opening(body, eta))
            return [[-1, witness]] + events(branch, context + [clause])
    raise ValueError('Malformed explicit proof')


def to_packets(certificate):
    explicit.verify(certificate)
    result = list(reversed(events(certificate['proof'], INITIAL))) + [certificate['goal']]
    verify_packets(result)
    return result


def reconstruct(goal, context, stream, trace):
    if goal[0] == goal[1]:
        trace.append({'packet': None, 'scope': len(context) - 1,
                      'rule': 'fixed reflexivity', 'goal': goal})
        return ['u', 0, goal[0], []]
    position = len(stream) - 1
    major, data = stream.pop()
    fresh = -len(context)
    row = {'packet': position, 'scope': len(context) - 1, 'goal': goal}
    trace.append(row)
    if type(major) is int:
        if major >= 0:
            row.update(rule='Use', clause=major, witness=data)
            antecedents, body = context[major + 1]
            premises = [reconstruct(a, context, stream, trace) for a in antecedents]
            return ['u', major + 1, data, premises]
        if major != -1:
            raise ValueError('Unknown introduction marker')
        row.update(rule='Close', witness=data, eigenvariable=fresh)
        body = explicit.opening(goal[1], data, 1)
        eta = fresh if goal[1][0] != 'd' and data == 0 else 0
        clause = ([], explicit.opening(body, eta))
        branch = reconstruct(explicit.opening(body, [fresh]), context + [clause], stream, trace)
        return ['i', goal, data, branch]
    if major[0] == 'd':
        row.update(rule='Open', source=major, eigenvariable=fresh)
        proof = reconstruct(major, context, stream, trace)
        body = explicit.opening(major[1], fresh, 1)
        clause = ([explicit.opening(body, 0)], body)
        branch = reconstruct(goal, context + [clause], stream, trace)
        return ['e', goal, proof, branch]
    row.update(rule='Step', first=major, second=data)
    return ['x', reconstruct(major, context, stream, trace), reconstruct(data, context, stream, trace)]


def to_explicit(certificate):
    goal = verify_packets(certificate)
    stream = copy.deepcopy(certificate[:-1])
    proof = reconstruct(goal, INITIAL, stream, [])
    if stream:
        raise ValueError('Decoder left trailing packets')
    result = {'goal': goal, 'proof': proof}
    explicit.verify(result)
    return result


def term_text(term):
    if type(term) is int:
        return '0' if term == 0 else f'#{term}' if term > 0 else f'a{-term}'
    if len(term) == 1:
        return f'S({term_text(term[0])})'
    return 'I(' + ', '.join(term_text(t) for t in term) + ')'


def formula_text(formula):
    if formula[0] == 'd':
        return 'D(' + formula_text(formula[1]) + ')'
    return term_text(formula[0]) + ' = ' + term_text(formula[1])


def format_packets(certificate):
    goal = verify_packets(certificate)
    trace = []
    reconstruct(goal, INITIAL, copy.deepcopy(certificate[:-1]), trace)
    lines = ['Goal: ' + formula_text(goal),
             'Packets below are listed in consumption order; #j is a bound index.']
    for event in trace:
        position = 'automatic' if event['packet'] is None else str(event['packet'])
        line = f"[{position}] scope {event['scope']}: {event['rule']}: {formula_text(event['goal'])}"
        if 'clause' in event:
            line += f"; clause {event['clause']}"
        if 'witness' in event:
            line += '; witness ' + term_text(event['witness'])
        if 'eigenvariable' in event:
            line += '; fresh ' + term_text(event['eigenvariable'])
        lines.append(line)
    return '\n'.join(lines) + '\n'


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in ('forward', 'backward', 'format'):
        raise SystemExit('usage: python translate.py forward|backward|format < certificate.json')
    certificate = json.load(sys.stdin)
    if sys.argv[1] == 'format':
        print(format_packets(certificate), end='')
    else:
        result = (to_packets if sys.argv[1] == 'forward' else to_explicit)(certificate)
        json.dump(result, sys.stdout, separators=(',', ':'))
        print()
