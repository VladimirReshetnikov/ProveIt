#!/usr/bin/env python3
"""Independently catalogue literal, unbounded countdown-loop summaries.

This parser/control evaluator does not import the search/frontier scripts.
It verifies each successful source edge against both exact path arithmetic
(retained carry zeros) and physical normalized-PC arithmetic (with overflow).
It then identifies CD-r positive cycles with CI/CB/CC bodies, no CI-r, and
records the exact affine register update, successful-source-step clock, and
physical-gap overflow count. Concrete probes validate the independently
derived closed forms; the unbounded argument is induction, in the companion
countdown_loops.md. No binary table is modified or certified by this script.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PROG = ROOT / 'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
PROG_SHA = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'


def strip_bits(path, bit, count):
    end = len(path)
    while count > 0 and end > 0:
        end -= 1
        if path[end] == bit:
            count -= 1
    return path[:end]


def exact_increment(path):
    # Literal list-style carry, retaining all cleared trailing positions.
    chars = list(path)
    index = len(chars) - 1
    while index >= 0 and chars[index] == '1':
        chars[index] = '0'
        index -= 1
    if index >= 0:
        chars[index] = '1'
    return ''.join(chars)


def physical_increment(path):
    # Deliberately a different implementation from exact_increment.
    last_zero = path.rfind('0')
    return ('', 1) if last_zero < 0 else (path[:last_zero] + '1', 0)


def next_pc(path, op, arg, zero=False, *, physical=False):
    if op == 'CI' or op == 'CD' and not zero:
        intermediate, increment = path, True
    elif op == 'CD':
        intermediate, increment = strip_bits(path, '0', 1), True
    elif op == 'CB':
        intermediate, increment = strip_bits(path, '0', arg), True
    elif op == 'CC':
        intermediate, increment = strip_bits(path, '1', arg), False
    else:
        raise ValueError(op)
    if physical:
        return physical_increment(intermediate) if increment else (intermediate.rstrip('0'), 0)
    return exact_increment(intermediate) if increment else intermediate


class Source:
    def __init__(self, raw):
        assert sha256(raw).hexdigest() == PROG_SHA
        body = raw.decode().split('Definition p254_tab : list (cedge * cedge) := [', 1)[1].split('].', 1)[0]
        edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
        self.nodes = [tuple(part.split() for part in pair) for pair in
                      re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', body)]
        self.sites, self.lookup = [], {}
        visited = set()

        def visit(node, prefix):
            assert node not in visited
            visited.add(node)
            for bit, (op, *arg) in enumerate(self.nodes[node]):
                path = prefix + str(bit)
                arg = int(arg[0]) if arg else None
                if op == 'CN':
                    visit(arg, path)
                else:
                    self.lookup[path] = len(self.sites)
                    self.sites.append((path, op, arg))
        visit(0, '')
        assert len(visited) == len(self.nodes) == 6459
        assert len(self.sites) == 6460

    def decode(self, pc):
        node, path = 0, ''
        for depth in range(len(self.nodes) + 1):
            bit = pc[depth] if depth < len(pc) else '0'
            path += bit
            op, *arg = self.nodes[node][int(bit)]
            if op == 'CN':
                node = int(arg[0])
            else:
                assert '1' not in pc[len(path):]
                return self.lookup[path]
        raise AssertionError('decoder did not reach a leaf')

    def edge(self, site, zero=False):
        path, op, arg = self.sites[site]
        assert op != 'CH'
        exact = next_pc(path, op, arg, zero)
        physical, overflow = next_pc(path, op, arg, zero, physical=True)
        assert exact.rstrip('0') == physical.rstrip('0')
        assert self.decode(exact) == self.decode(physical)
        return self.decode(exact), overflow, exact, physical.rstrip('0')

    def concrete_step(self, pc, values):
        site = self.decode(pc)
        path, op, arg = self.sites[site]
        zero = op == 'CD' and values[arg] == 0
        if op == 'CI':
            values[arg] += 1
        elif op == 'CD' and not zero:
            assert values[arg] > 0
            values[arg] -= 1
        else:
            assert op in ('CD', 'CB', 'CC')
        _, overflow, exact, _ = self.edge(site, zero)
        return exact, overflow


def catalogue(source):
    loops = []
    all_edges = 0
    for site, (_, op, _) in enumerate(source.sites):
        if op == 'CH':
            continue
        for zero in (True, False) if op == 'CD' else (False,):
            source.edge(site, zero)
            all_edges += 1
    for head, (path, op, counter) in enumerate(source.sites):
        if op != 'CD':
            continue
        current, gap, _, _ = source.edge(head, False)
        body, seen, increments = [], set(), [0] * 9
        while current != head:
            if current in seen:
                break
            seen.add(current)
            _, kind, register = source.sites[current]
            if kind not in ('CI', 'CB', 'CC') or kind == 'CI' and register == counter:
                break
            body.append(current)
            if kind == 'CI':
                increments[register] += 1
            current, overflow, _, _ = source.edge(current)
            gap += overflow
        else:
            exit_site, zero_gap, exact_exit, normalized_exit = source.edge(head, True)
            loops.append({
                'head_site': head, 'head_path': path, 'counter': counter,
                'body_sites': body, 'positive_cycle_source_steps': len(body) + 1,
                'increments_per_positive_cycle': increments,
                'positive_cycle_gap_increment': gap,
                'zero_exit_gap_increment': zero_gap,
                'zero_exit_site': exit_site, 'zero_exit_exact_pc': exact_exit,
                'zero_exit_normalized_pc': normalized_exit,
            })
    return loops, all_edges


def concrete_controls(source, loops):
    probes, steps = 0, 0
    for record in loops:
        for counter_value in (0, 1, 2, 5):
            # Distinct non-counter entries exercise preservation and addition.
            original = [(record['head_site'] + 3 * j) % 7 for j in range(9)]
            original[record['counter']] = counter_value
            expected = [a + b * counter_value for a, b in
                        zip(original, record['increments_per_positive_cycle'])]
            expected[record['counter']] = 0
            count = record['positive_cycle_source_steps'] * counter_value + 1
            values, pc, gap = original.copy(), record['head_path'], 0
            for _ in range(count):
                pc, overflow = source.concrete_step(pc, values)
                gap += overflow
            assert values == expected
            assert pc == record['zero_exit_exact_pc']
            assert source.decode(pc) == record['zero_exit_site']
            assert gap == (record['positive_cycle_gap_increment'] * counter_value
                           + record['zero_exit_gap_increment'])
            probes += 1
            steps += count
    return {'probes': probes, 'successful_source_steps': steps,
            'counter_values': [0, 1, 2, 5],
            'scope': 'Finite regression controls; the unbounded theorem uses induction.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('countdown_loop_catalogue.json'))
    args = parser.parse_args()
    source = Source(PROG.read_bytes())
    loops, all_edges = catalogue(source)
    assert len(loops) == 1433
    assert all(loop['positive_cycle_gap_increment'] == 0 for loop in loops)
    controls = concrete_controls(source, loops)
    summary = {
        'simple_countdown_loops': len(loops),
        'all_nonhalting_control_edges_cross_checked': all_edges,
        'cycle_length_histogram': dict(sorted(Counter(loop['positive_cycle_source_steps'] for loop in loops).items())),
        'counter_histogram': dict(sorted(Counter(loop['counter'] for loop in loops).items())),
        'zero_exit_gap_histogram': dict(sorted(Counter(loop['zero_exit_gap_increment'] for loop in loops).items())),
        'maximum_increment_count_per_register_per_cycle': max(max(loop['increments_per_positive_cycle']) for loop in loops),
        'regression_controls': controls,
    }
    output = {'status': 'PASS ordinary source-loop catalogue and controls; no binary simulation claim',
              'source_sha256': PROG_SHA, 'checker_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
              'summary': summary, 'loops': loops}
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    examples = []
    seen_types = set()
    for loop in loops:
        kind = sum(loop['increments_per_positive_cycle'])
        if kind not in seen_types:
            seen_types.add(kind)
            examples.append({**loop, 'body_instructions': [source.sites[x] for x in loop['body_sites']]})
    print(json.dumps({'examples': examples}, indent=2))


if __name__ == '__main__':
    main()
