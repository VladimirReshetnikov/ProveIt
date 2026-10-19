#!/usr/bin/env python3
"""Independent literal binding audit for the selected K226 Rocq development.

Uses only Python's standard library. It does not import any generator or
construction checker. Exact literal parsing is deliberately strict. This is
an artifact-binding audit, not a replacement for the Rocq kernel check.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re


PINS = {
    'dense_table': 'b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599',
    'sparse_table': '6f5a35c58961c77baf595ab743a185f4df6815aaaceb89a5b1494521b96f1d6c',
    'sites': '47f5cfac0ec765c6f84f9d29973d4c9b3d79f12482a2cd1268d582e85c814bd3',
}
DELETED = {65, 79, 140, 175}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(text):
    """Remove nested Rocq comments, retaining separating whitespace."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i + 2] == '(*':
            depth += 1
            out.append(' ')
            i += 2
        elif text[i:i + 2] == '*)':
            require(depth > 0, 'Unmatched Rocq comment terminator')
            depth -= 1
            out.append(' ')
            i += 2
        else:
            out.append(' ' if depth else text[i])
            i += 1
    require(depth == 0, 'Unterminated Rocq comment')
    return ''.join(out)


def definition(text, name):
    pattern = r'\bDefinition\s+' + re.escape(name) + r'\b.*?:=(.*?)\.'
    matches = re.findall(pattern, without_comments(text), flags=re.S)
    require(len(matches) == 1, 'Expected exactly one definition of ' + name)
    return matches[0].strip()


def list_body(text, name):
    body = definition(text, name)
    require(body.startswith('[') and body.endswith(']'), name + ' is not a literal list')
    return body[1:-1]


def parse_table_v(path, name):
    body = list_body(path.read_text(), name)
    entries = [x.strip() for x in body.split(';') if x.strip()]
    row = re.compile(r'\((true|false),\s*([LR]),\s*(\d+),\s*'
                     r'(true|false),\s*([LR]),\s*(\d+)\)')
    table = {}
    for q, entry in enumerate(entries):
        match = row.fullmatch(entry)
        require(match is not None, 'Nonliteral table row in ' + str(path))
        a, d, n, b, e, m = match.groups()
        table[q, 0] = (int(a == 'true'), d, int(n))
        table[q, 1] = (int(b == 'true'), e, int(m))
    return table


def parse_tm(path):
    lines = path.read_text().splitlines()
    require(lines and lines[0] == '#! start 0', 'Wrong initial state/header in ' + str(path))
    table = {}
    for line in lines[1:]:
        if not line.strip() or line.startswith('#'):
            continue
        match = re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)', line)
        require(match is not None, 'Malformed literal machine row')
        q, b, w, d, n = match.groups()
        key = (int(q), int(b))
        require(key not in table, 'Duplicate literal machine row')
        table[key] = (int(w), d, int(n))
    return table


def parse_source(path):
    text = path.read_text()
    entries = [x.strip() for x in list_body(text, 'p226_tab').split(';') if x.strip()]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    pair = re.compile(r'\((' + edge + r'),\s*(' + edge + r')\)')
    rows = []
    for entry in entries:
        match = pair.fullmatch(entry)
        require(match is not None, 'Nonliteral source table row')
        rows.append(match.groups())
    require(len(rows) == 188, 'Unexpected source decision-node count')

    # Check that the actual program record is connected to the parsed table.
    expected = "{|nodes:=funn=>let'(a,b):=nthnp226_tab(CH,CH)in(cva,cvb);root:=187;nnodes:=188|}"
    actual = re.sub(r'\s+', '', definition(text, 'p226'))
    require(actual == expected, 'Unexpected p226 record or table binding')

    sites = []

    def walk(node, prefix):
        for bit, item in enumerate(rows[node]):
            words = item.split()
            opcode = words[0]
            value = int(words[1]) if len(words) > 1 else None
            address = prefix + str(bit)
            if opcode == 'CN':
                require(0 <= value < node, 'Source table is not a backward-reference DAG')
                walk(value, address)
            else:
                sites.append([address, opcode, value])

    walk(187, '')
    return rows, sites


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rocq', type=Path, required=True,
                        help='Directory containing the selected K226 Rocq modules')
    parser.add_argument('--dense-table', type=Path, required=True)
    parser.add_argument('--sparse-table', type=Path, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()

    inputs = {'dense_table': args.dense_table, 'sparse_table': args.sparse_table,
              'sites': args.sites}
    for name, path in inputs.items():
        require(digest(path) == PINS[name], 'Selected artifact hash mismatch: ' + name)

    dense = parse_tm(args.dense_table)
    sparse = parse_tm(args.sparse_table)
    dense_v = parse_table_v(args.rocq / 'Table226.v', 'table226')
    sparse_v = parse_table_v(args.rocq / 'Table230.v', 'table230')
    require(len(dense) == len(sparse) == 452, 'Unexpected machine row count')
    require(len(sparse_v) == 460, 'Sparse Rocq table must retain 230 data rows')
    require(dense == dense_v, 'Rocq dense table differs from selected literal artifact')
    retained = sorted(set(range(230)) - DELETED)
    require(set(sparse) == {(q, b) for q in retained for b in (0, 1)},
            'Wrong sparse working-state domain')
    require(set(dense) == {(q, b) for q in range(226) for b in (0, 1)},
            'Wrong dense working-state domain')
    require(all(sparse_v[key] == value for key, value in sparse.items()),
            'Rocq sparse table differs at a surviving row')
    require(all(target <= 226 for w, d, target in dense.values()),
            'Dense target exceeds the separate halt state')
    require(all(target in retained or target == 230 for w, d, target in sparse.values()),
            'Sparse row targets a disabled or invalid state')

    # Derive dense-to-sparse renumbering independently from the deleted set.
    expand = retained + [230]
    commuting_cases = 0
    for q in range(227):
        for bit in (0, 1):
            dr = dense.get((q, bit))
            sr = sparse.get((expand[q], bit))
            mapped = None if dr is None else (dr[0], dr[1], expand[dr[2]])
            require(sr == mapped, 'Dense/sparse literal transition does not commute')
            commuting_cases += 1
    require(expand[0] == 0 and expand[226] == 230, 'Start/halt renumbering mismatch')

    nodes, sites = parse_source(args.rocq / 'Prog226.v')
    selected_sites = json.loads(args.sites.read_text())
    require(sites == selected_sites, 'Rocq source differs in address, opcode, or argument')
    require(len(sites) == 5121, 'Unexpected source leaf count')

    modules = ['OffsetBisim230.v', 'Source226.v', 'Prog226.v', 'Cert226Offsets.v',
               'TM230.v', 'Table230.v', 'Table226.v', 'Dense226.v',
               'Correct226.v', 'CorrectDense226.v', 'Boot230.v', 'Sim230Main.v']
    receipt = {
        'status': 'INDEPENDENT_K226_ROCQ_LITERAL_BINDINGS_PASS',
        'implementation': 'Python standard library only; no generator imports',
        'artifact_sha256': PINS,
        'dense_transition_rows_compared': 452,
        'sparse_surviving_transition_rows_compared': 452,
        'sparse_disabled_states': sorted(DELETED),
        'transition_commuting_cases_including_halt': commuting_cases,
        'dense_start': 0, 'dense_halt': 226, 'sparse_start': 0, 'sparse_halt': 230,
        'source_decision_nodes': len(nodes),
        'source_leaf_paths_opcodes_and_arguments_compared': len(sites),
        'source_maximum_depth': max(len(site[0]) for site in sites),
        'source_record_connected_to_parsed_table': True,
        'reviewed_rocq_module_sha256': {name: digest(args.rocq / name) for name in modules},
        'scope': 'Exact artifact bindings and literal renumbering only. The written '
                 'independent review covers theorem statements and proof structure; '
                 'the companion Rocq build/kernel check verifies proof terms.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
