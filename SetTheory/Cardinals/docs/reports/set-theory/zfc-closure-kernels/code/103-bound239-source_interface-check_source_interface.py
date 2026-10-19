#!/usr/bin/env python3
"""Exact static extraction of the pinned Lean source DAG and logical seed.

This is a stdlib data/interface check, not a Lean elaborator or theorem checker.
Run from any directory. Inputs default to sibling package folders.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Run without -O/-OO: assertions are required.')

HERE = Path(__file__).resolve().parent
BASE_SOURCE_SHA256 = '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
LEAN_COMMIT = '13ec39ed43148b1807f51ed6e6528e1c84659562'
LEAF = {'inc': 'CI', 'decnz': 'CD', 'brk': 'CB', 'cont': 'CC', 'halt': 'CH'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def uncomment(s):
    """Remove Lean line comments and nested block comments before extraction."""
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1
            i += 2
            if not depth:
                out.append(' ')
        elif depth:
            i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i])
            i += 1
    assert depth == 0
    return ''.join(out)


def edge(s):
    m = re.fullmatch(r'\s*\.(node|inc|decnz|brk|cont)\s+(\d+)\s*', s)
    if m:
        return m[1], int(m[2])
    assert s.strip() == '.halt', s
    return 'halt', None


def literal_rows(text):
    rows = {}
    lines = [s for s in text.splitlines() if s.startswith('private def row')]
    for line in lines:
        m = re.fullmatch(r'private def row(\d{3}) : Row := \((.*)\)', line)
        assert m, line
        n = int(m[1])
        assert n not in rows
        pair = m[2].split(',')
        assert len(pair) == 2
        pair = [part.strip() for part in pair]
        pair = [part[1:-1] if part.startswith('(') and part.endswith(')') else part for part in pair]
        rows[n] = tuple(map(edge, pair))
    assert set(rows) == set(range(203))
    return rows


def lookup_tree(text):
    body = text.split('private def rawLookup (n : Nat) : Row :=', 1)[1]
    body = body.split('def nodes (n : Nat) : Row :=', 1)[0]
    token_re = r'row\d{3}|if|then|else|n|<|\d+'
    assert not re.sub(token_re, '', body).strip()
    tokens = re.findall(token_re, body)
    cursor = 0

    def parse():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token.startswith('row'):
            return int(token[3:])
        assert token == 'if'
        assert tokens[cursor:cursor+2] == ['n', '<']
        threshold = int(tokens[cursor+2])
        assert tokens[cursor+3] == 'then'
        cursor += 4
        left = parse()
        assert tokens[cursor] == 'else'
        cursor += 1
        return threshold, left, parse()

    tree = parse()
    assert cursor == len(tokens)
    return tree


def lookup(tree, n):
    while not isinstance(tree, int):
        k, left, right = tree
        tree = left if n < k else right
    return tree


def overrides(text, fallback):
    m = re.search(r'def nodes \(n : Nat\) : [^\n]*:=\s*(.*?)\ndef program\b', text, re.S)
    assert m
    pieces = re.split(r'\belse\b', m[1])
    assert pieces.pop().strip() == fallback + '.program.nodes n'
    result = {}
    for piece in pieces:
        m = re.fullmatch(r'\s*if n = (\d+) then \(([^(),]*), ([^(),]*)\)\s*', piece)
        assert m, piece
        n = int(m[1])
        assert n not in result
        result[n] = edge(m[2]), edge(m[3])
    m = re.search(r'def program : [^\n]* where\s*(.*?)\ntheorem\b', text, re.S)
    assert m
    assert m[1].split() == ('nodes := nodes root := ' + fallback + '.program.root nnodes := ' + fallback + '.program.nnodes').split()
    return result


def extract_program(texts):
    text = texts['ProgramRouting245.lean']
    rows = literal_rows(text)
    tree = lookup_tree(text)
    resolved = [lookup(tree, n) for n in range(203)]
    assert resolved == list(range(203)), resolved
    assert re.search(r'def nodes \(n : Nat\) : Row :=\s*if n < 203 then rawLookup n else \(\.halt, \.halt\)\s*def program', text)
    m = re.search(r'def program : Program where\s*(.*?)\ntheorem\b', text, re.S)
    assert m and m[1].split() == 'nodes := nodes root := 202 nnodes := 203'.split()
    ov244 = overrides(texts['ProgramRotation244.lean'], 'ProgramRouting245')
    ov240 = overrides(texts['SourceRotation240.lean'], 'ProgramRotation244')
    assert set(ov244) == {5, 6} and set(ov240) == {169}
    rows.update(ov244)
    rows.update(ov240)
    result, reached, counts = [], set(), Counter()

    def expand(n, path):
        reached.add(n)
        counts[n] += 1
        for bit, (op, arg) in enumerate(rows[n]):
            newpath = path + str(bit)
            if op == 'node':
                assert 0 <= arg < n
                expand(arg, newpath)
            else:
                result.append([newpath, LEAF[op], arg])

    expand(202, '')
    return result, reached, counts, {**ov244, **ov240}


def extract_seed(texts):
    l2 = texts['L2Lib254.lean']
    body = l2.split('structure AS where', 1)[1].split('def enc', 1)[0]
    fields = re.findall(r'^\s+(\w+) : Nat\s*$', body, re.M)
    assert fields == ['np', 'tw', 'ws', 'ac', 'p1', 'p2', 's1', 's2', 'pl']
    body = l2.split('def enc (st : AS) : Regs', 1)[1].split('abbrev Rn', 1)[0]
    entries = re.findall(r'\| (\d+) => st\.(\w+)', body)
    assert [(int(i), f) for i, f in entries] == list(enumerate(fields))
    assert body.count('| _ => 0') == 1
    assert re.sub(r'\| \d+ => st\.\w+|\| _ => 0', '', body).strip() == ''
    seed = texts['LogicalSeed246.lean']
    m = re.search(r'def seed : L2\.AS := ⟨([\d, ]+)⟩', seed)
    assert m
    values = [int(v) for v in m[1].split(',')]
    assert len(values) == len(fields)
    assert re.search(r'def registers : RegisterPath\.Registers := L2\.enc seed\s*def initial : RegisterPath\.Configuration := ⟨\[\], registers⟩', seed)
    return dict(zip(fields, values)), values


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sites', type=Path, default=HERE.parent/'baseline/rotation240/sites_logical.json')
    ap.add_argument('--blank-prefix', type=Path, default=HERE.parent/'candidate239/blank_prefix.json')
    ap.add_argument('--output', type=Path, default=HERE/'interface_result.json')
    args = ap.parse_args()
    pins = json.loads((HERE/'source_pins.json').read_text())
    texts, checked = {}, []
    for pin in pins:
        data = (HERE/pin['file']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        assert blob == pin['git_blob_sha'], pin['file']
        assert pin['commit'] == LEAN_COMMIT
        texts[pin['file']] = uncomment(data.decode())
        checked.append({**pin, 'sha256': hashlib.sha256(data).hexdigest()})
    sites, reached, occurrences, override = extract_program(texts)
    assert sha256(args.sites) == BASE_SOURCE_SHA256
    pinned_sites = json.loads(args.sites.read_text())
    assert sites == pinned_sites, 'Lean unfolding does not equal every ordered source triple'
    record, logical = extract_seed(texts)
    blank = json.loads(args.blank_prefix.read_text())
    assert blank['logical_registers'] == logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert blank['pc'] == ''
    frame = texts['BootstrapFrameRotation240.lean']
    assert re.search(r'def spares : List Nat := List\.replicate 167 1', frame)
    m = re.search(r'theorem physical_seed :\s*vregs LogicalSeed246\.initial\.registers = (\[[\d, ]+\]) :=', frame)
    assert m
    physical = json.loads(m[1])
    assert blank['physical_registers'] == physical == [0, 0, 0, 3, 0, 0, 3, 0, 0]
    assert blank['spare_values'] == [1]*167
    assert (blank['steps'], blank['final_head'], blank['header_distance']) == (409691, -5, 181)
    # Pin the imported frame's literal shape; full binary startup is checked elsewhere.
    target = frame.split('def target : ZipConfig 240 :=', 1)[1].split('theorem target_zip', 1)[0]
    assert target.split() == ('{ state := some ⟨84, by decide⟩, head := -5, '
        'left := true :: List.replicate 9 false, '
        'right := List.replicate 181 false ++ [true] ++ '
        'registerBits ([0, 0, 0, 3, 0, 0, 3, 0, 0] ++ spares) ++ '
        'List.replicate 0 false }').split()
    report = {
        'status': 'EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS',
        'scope': 'Static data extraction; no Lean dependency build or theorem kernel replay.',
        'lean_commit': LEAN_COMMIT,
        'source_files': checked,
        'source_sites_sha256': BASE_SOURCE_SHA256,
        'source_program': 'SetTheory.BusyBeaver.ZFC.SourceRotation240.program',
        'root': 202, 'declared_storage_bound': 203,
        'raw_lookup_all_203_indices_verified': True,
        'reachable_internal_nodes': len(reached),
        'unreachable_internal_nodes': sorted(set(range(203))-reached),
        'overrides': override,
        'row169_occurrences': occurrences[169],
        'ordered_source_triples_exactly_equal': len(sites),
        'guards': len(sites)+sum(op == 'CD' for _, op, _ in sites),
        'max_path_length': max(len(p) for p, _, _ in sites),
        'max_path_zero_run': max(max(map(len, p.split('1'))) for p, _, _ in sites),
        'distinct_leaf_kinds': len(set((op, v) for _, op, v in sites)),
        'seed': {'name': 'LogicalSeed246.initial', 'pc': '', 'record': record,
                 'logical_registers': logical, 'registers_at_indices_ge_9': 0,
                 'physical_registers': physical, 'spare_count': 167, 'spare_value': 1},
        'blank_prefix_sha256': sha256(args.blank_prefix),
        'blank_prefix_steps': blank['steps'],
        'bootstrap_frame_literal_shape_matches': True,
    }
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ['status', 'ordered_source_triples_exactly_equal',
        'guards', 'reachable_internal_nodes', 'row169_occurrences', 'max_path_length',
        'max_path_zero_run', 'blank_prefix_steps']}, indent=2))


if __name__ == '__main__':
    main()
