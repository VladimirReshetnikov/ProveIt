#!/usr/bin/env python3
"""Independently bind the frozen Rocq program/table literals to release data.

This parses a restricted literal grammar; it never imports or evaluates the
Rocq sources or the upstream generators. Every list entry must be consumed.
Besides literal equality, it recomputes the source height and escape tables.
This is a finite arithmetic check, not a replacement for Rocq compilation.
All checks remain active under python -O.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def clean_coq(s):
    """Erase nested comments; quoted strings are rejected in these literals."""
    i = depth = 0
    out = []
    while i < len(s):
        if s.startswith('(*', i):
            depth += 1
            i += 2
        elif depth and s.startswith('*)', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            require(s[i] != '"', 'Unexpected quoted string in literal source')
            out.append(s[i])
            i += 1
    require(depth == 0, 'Unterminated nested Rocq comment')
    return ''.join(out)


def compact(s):
    return re.sub(r'\s+', '', s)


def get_definition(code, name):
    """A qualified identifier's internal dot is not a command terminator."""
    pattern = r'\bDefinition\s+' + re.escape(name) + r'\b(?P<tail>.*?)\.(?=\s|$)'
    matches = list(re.finditer(pattern, code, re.S))
    require(len(matches) == 1, f'Expected exactly one literal definition {name}')
    return matches[0].group('tail')


def get_list(code, name, expected_type):
    definition = get_definition(code, name)
    m = re.fullmatch(r'\s*:\s*(.*?)\s*:=\s*\[\s*(.*?)\s*\]\s*', definition, re.S)
    require(m is not None, f'Nonliteral list definition: {name}')
    require(compact(m[1]) == compact(expected_type), f'Wrong literal type: {name}')
    entries = m[2].split(';') if m[2] else []
    if entries and not entries[-1].strip():
        entries.pop()
    require(all(x.strip() for x in entries), f'Empty list entry in {name}')
    return entries


def parse_program(code):
    expected_cv = """(e : cedge) : edge := match e with
      | CN m => ENode (N.to_nat m) | CI r => EInc r
      | CD r => EDecnz r | CB k => EBreak k
      | CC k => EContinue k | CH => EHalt end"""
    require(compact(get_definition(code, 'cv')) == compact(expected_cv),
            'The cedge-to-edge conversion differs from the audited semantics')
    rows = []
    edge_rx = r'(CN|CI|CD|CB|CC|CH)(?:\s+([0-9]+))?'
    row_rx = re.compile(r'\s*\(\s*' + edge_rx + r'\s*,\s*' + edge_rx + r'\s*\)\s*')
    for i, entry in enumerate(get_list(code, 'p230_tab', 'list (cedge * cedge)')):
        m = row_rx.fullmatch(entry)
        require(m is not None, f'Unparsed p230_tab entry {i}')
        pair = []
        for k in (1, 3):
            op, arg = m[k], m[k + 1]
            require((arg is None) == (op == 'CH'), f'Malformed edge at node {i}')
            pair.append((op, None if arg is None else int(arg)))
        rows.append(tuple(pair))
    expected_p = """: prog := {| nodes := fun n => let '(a, b) :=
      nth n p230_tab (CH, CH) in (cv a, cv b); root := 0; nnodes := 5124 |}"""
    require(compact(get_definition(code, 'p230')) == compact(expected_p),
            'The p230 root/node lookup differs from the audited literal binding')
    require(len(rows) == 5124, 'Wrong number of source cons cells')
    require(compact(get_definition(code, 'R0')) ==
            compact(': regs := upd (upd regs0 0 3) 4 3'),
            'Wrong nonzero logical initial register file')
    for n, pair in enumerate(rows):
        for op, arg in pair:
            if op == 'CN':
                require(n < arg < len(rows), f'Bad acyclic source edge {n} -> {arg}')
            elif op in ('CI', 'CD'):
                require(0 <= arg < 9, 'Out-of-range primary register')
            elif op in ('CB', 'CC'):
                require(arg > 0, 'Zero-level break or continue')
    return rows


def reconstruct_program(rows):
    names = {'CI': 'EInc', 'CD': 'EDecnz', 'CB': 'EBreak',
             'CC': 'EContinue', 'CH': 'EHalt'}
    leaves, visited = [], Counter()
    stack = [('', 0)]
    while stack:
        path, n = stack.pop()
        visited[n] += 1
        require(visited[n] == 1, f'Unexpected sharing in expanded tree at {n}')
        for bit in (1, 0):
            op, arg = rows[n][bit]
            child_path = path + str(bit)
            if op == 'CN':
                stack.append((child_path, arg))
            else:
                leaves.append([child_path, names[op] + ('' if arg is None else ' ' + str(arg))])
    require(set(visited) == set(range(len(rows))), 'Unreachable literal source node')
    leaves.sort()
    logical = [[path, {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB',
                       'EContinue': 'CC', 'EHalt': 'CH'}[op.split()[0]],
                None if op == 'EHalt' else int(op.split()[1])]
               for path, op in leaves]
    H, B, C, structures = [None] * len(rows), [None] * len(rows), [None] * len(rows), [None] * len(rows)

    def edge_data(e):
        op, arg = e
        if op == 'CN':
            return H[arg], B[arg], C[arg], structures[arg]
        return 0, (1 if op == 'CD' else arg if op == 'CB' else 0), (arg if op == 'CC' else 0), e

    for n in reversed(range(len(rows))):
        ah, ab, ac, ast = edge_data(rows[n][0])
        bh, bb, bc, bst = edge_data(rows[n][1])
        H[n], B[n], C[n] = 1 + max(ah, bh), max(ab - 1, bb), max(ac, bc - 1)
        structures[n] = (ast, bst)
    require(B[0] == C[0] == 0, 'A source break or continue can escape the root')
    require(H[0] <= len(rows) + 1, 'Height fails the source walk fuel bound')
    return leaves, logical, (H, B, C), len(set(structures))


def parse_table(code):
    rows = {}
    pattern = re.compile(r'\s*\(\s*(true|false)\s*,\s*(L|R)\s*,\s*([0-9]+)\s*,\s*'
                         r'(true|false)\s*,\s*(L|R)\s*,\s*([0-9]+)\s*\)\s*')
    for q, entry in enumerate(get_list(code, 'table230', 'list (bool * dir * nat * bool * dir * nat)')):
        m = pattern.fullmatch(entry)
        require(m is not None, f'Unparsed table230 entry {q}')
        for b, k in ((0, 1), (1, 4)):
            w, d, z = int(m[k] == 'true'), m[k + 1], int(m[k + 2])
            require(0 <= z <= 230, 'Transition clamped by the Rocq bounded-state wrapper')
            rows[q, b] = (w, d, z)
    require(set(rows) == {(q, b) for q in range(230) for b in (0, 1)}, 'Wrong table state set')
    return rows


def parse_release_table(raw):
    rows, start = {}, None
    for i, line in enumerate(raw.decode('utf-8').splitlines(), 1):
        if line.startswith('#! start '):
            require(start is None, 'Multiple initial-state directives')
            start = int(line[9:])
        elif line and not line.startswith('#'):
            m = re.fullmatch(r'(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)', line)
            require(m is not None, f'Unparsed release table line {i}')
            q, b, w, d, z = int(m[1]), int(m[2]), int(m[3]), m[4], int(m[5])
            require((q, b) not in rows, 'Duplicate release transition')
            rows[q, b] = (w, d, z)
    require(start == 0, 'Release machine does not start in state 0')
    return rows


def canonical_hash(data):
    return hashlib.sha256((json.dumps(data, separators=(',', ':')) + '\n').encode()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2] / 'input/k230-rocq')
    p.add_argument('--out', type=Path, default=Path(__file__).with_name('k230_literal_bindings.json'))
    a = p.parse_args()
    names = ['coq/tm/Prog230.v', 'coq/tm/Table230.v', 'coq/tm/TM230.v',
             'machine/k230.tm', 'machine/sites230.json']
    raw = {name: (a.repo / name).read_bytes() for name in names}
    code = {name: clean_coq(data.decode('utf-8')) for name, data in raw.items() if name.endswith('.v')}
    rows = parse_program(code['coq/tm/Prog230.v'])
    leaves, logical, hbc, distinct_nodes = reconstruct_program(rows)
    supplied = json.loads(raw['machine/sites230.json'])
    require(leaves == supplied, 'Rocq source leaves differ from released sites230.json')
    for name, values in zip(('p230_H', 'p230_B', 'p230_C'), hbc):
        entries = get_list(code['coq/tm/Prog230.v'], name, 'list nat')
        require(all(re.fullmatch(r'\s*[0-9]+\s*', x) for x in entries), f'Nonliteral natural in {name}')
        require([int(x) for x in entries] == values, f'Wrong exported well-formedness table {name}')
    tm = parse_table(code['coq/tm/Table230.v'])
    require(tm == parse_release_table(raw['machine/k230.tm']), 'Rocq table differs from released k230.tm')
    wrapper = compact(code['coq/tm/TM230.v'])
    for snippet in ('Definition NH := 230.', 'Definition q0 := st 0.', 'Definition s0 := false.',
                    'match nth_error table230 q with | None => None | Some (w0, d0, n0, w1, d1, n1) => if s then Some (w1, d1, n1) else Some (w0, d0, n0) end.',
                    'Definition tm : TM := fun \'(q, s) => match tmn (bval q) s with | None => None | Some (w, d, n) => Some (w, d, st n) end.'):
        require(compact(snippet) in wrapper, 'Rocq table wrapper differs from audited semantics')
    receipt = {
        'status': 'PASS_INDEPENDENT_ROCQ_RELEASE_LITERAL_BINDINGS',
        'source': {
            'expanded_cons_nodes': len(rows), 'leaf_occurrences': len(leaves),
            'distinct_cons_subtrees': distinct_nodes, 'root': 0,
            'height': hbc[0][0], 'root_break_escape': hbc[1][0], 'root_continue_escape': hbc[2][0],
            'logical_initial_registers': [3, 0, 0, 0, 3, 0, 0, 0, 0],
            'all_leaf_paths_and_opcodes_equal_release': True,
            'complete_acyclic_tree': True, 'all_height_break_continue_entries_recomputed': True,
            'canonical_logical_triples_sha256': canonical_hash(logical)
        },
        'machine': {'working_states': 230, 'literal_transitions': len(tm), 'initial_state': 0,
                    'blank_symbol': 0, 'halt': 230, 'all_rows_equal_release': True,
                    'bounded_state_wrapper_never_clamps_targets': True},
        'inputs_sha256': {name: hashlib.sha256(data).hexdigest() for name, data in raw.items()},
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Exact finite literal binding and source well-formedness arithmetic. No fresh Rocq compile or kernel assumption audit is claimed.'
    }
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
