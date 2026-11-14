#!/usr/bin/env python3
"""Compare the six supplied U209 snapshots, without proposal-code imports.

Usage: python3 compare_snapshots.py --root PACKAGE --output comparison.json
--root may also name PACKAGE/comparison. All source words, source control graphs,
literal transition graphs, and reported relabelings are compared as data, not
merely by hashes. PDF extraction is rerun when pdftotext is installed; use
--require-pdf-extraction to make that optional external tool mandatory.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import re
import shutil
import subprocess

NAMES = ('plain', 'compatibility', 'compatible_folds', 'composed', 'joint',
         'joint_pdf_only')
CLASS_A = {'plain', 'compatible_folds', 'composed', 'joint', 'joint_pdf_only'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def jsha(value):
    return sha(json.dumps(value, separators=(',', ':')).encode())


def read_table(path):
    rows, starts = {}, []
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        if not line.strip() or line.startswith('#'):
            continue
        parts = line.split()
        need(len(parts) == 5, 'Malformed transition row: ' + str(path))
        q, b, w, d, r = parts
        q, b, w, r = map(int, (q, b, w, r))
        need((q, b) not in rows and b in (0, 1) and w in (0, 1)
             and d in ('L', 'R'), 'Invalid or duplicate transition')
        rows[q, b] = (w, d, r)
    states = {q for q, b in rows}
    need(starts == [0] and 0 in states, 'Expected sole start declaration 0')
    need(len(states) == 209 and len(rows) == 418
         and set(rows) == {(q, b) for q in states for b in (0, 1)},
         'Expected complete binary 209-working-state table')
    halts = {r for w, d, r in rows.values()} - states
    need(len(halts) == 1, 'Expected unique separate halt label')
    return rows, next(iter(halts))


def canonical(table, halt):
    """Fixed edge order makes BFS names canonical for a rooted labeled graph."""
    ids, queue, result = {0: 0}, [0], []
    for q in queue:
        pair = []
        for bit in (0, 1):
            w, d, target = table[q, bit]
            if target == halt:
                value = 'H'
            else:
                if target not in ids:
                    ids[target] = len(ids)
                    queue.append(target)
                value = ids[target]
            pair.append([w, d, value])
        result.append(pair)
    need(len(ids) == 209, 'Working state not graph-reachable from start')
    return result


def forced_mapping(left, right):
    """Construct or refute the map forced by start and read-labeled paths."""
    a, ah = left
    b, bh = right
    rho, inverse = {0: 0, ah: bh}, {0: 0, bh: ah}
    first_path = {0: '', ah: 'halt'}
    queue = [(0, 0, '')]
    for q, s, word in queue:
        for bit in (0, 1):
            w, d, t = a[q, bit]
            v, e, u = b[s, bit]
            witness = dict(read_word=word + str(bit),
                           left_row=[q, bit, w, d, t],
                           right_row=[s, bit, v, e, u])
            if (w, d) != (v, e):
                return dict(isomorphic=False, witness=dict(
                    kind='different write or direction', **witness))
            if (t == ah) != (u == bh):
                return dict(isomorphic=False, witness=dict(
                    kind='halt versus working state', **witness))
            if t in rho and rho[t] != u:
                return dict(isomorphic=False, witness=dict(
                    kind='forced state map conflict', earlier_word=first_path[t],
                    earlier_target=rho[t], **witness))
            if u in inverse and inverse[u] != t:
                return dict(isomorphic=False, witness=dict(
                    kind='forced map is not injective', earlier_left=inverse[u],
                    earlier_word=first_path[inverse[u]], **witness))
            if t not in rho:
                rho[t], inverse[u], first_path[t] = u, t, word + str(bit)
                queue.append((t, u, word + str(bit)))
    need(len(rho) == 210 and len(inverse) == 210, 'Incomplete isomorphism')
    need(all(b[rho[q], bit] == (w, d, rho[t])
             for (q, bit), (w, d, t) in a.items()), 'Row-map verification failed')
    return dict(isomorphic=True, mapping=rho, rows_verified=418)


def source_graph(path):
    """Validate the full source tree and resolve both guarded ordinal graphs.

CI increments and advances; CD has zero/positive successors; CB exits through
its kth enclosing zero edge; CC repeats through its kth enclosing one edge.
The second resolver implements binary address increment/cut independently.
"""
    rows = json.loads(path.read_text())
    need(len(rows) == 3909, 'Wrong primitive count')
    trie = {}
    for address, op, arg in rows:
        need(address and set(address) <= {'0', '1'}, 'Bad source address')
        need(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Bad opcode')
        need((op == 'CH' and arg is None) or
             (op != 'CH' and type(arg) is int and arg >= 0), 'Bad operand')
        need(op not in ('CI', 'CD') or arg < 9, 'Bad register')
        need(op not in ('CB', 'CC') or arg >= 1, 'Bad control depth')
        node = trie
        for bit in address:
            need('leaf' not in node, 'Source leaf overlaps a prefix')
            node = node.setdefault(bit, {})
        need(not node, 'Duplicate or overlapping source leaf')
        node['leaf'] = [op, arg]
    intervals, ordered = {}, []

    def visit(node, address):
        begin = len(ordered)
        if 'leaf' in node:
            need(set(node) == {'leaf'}, 'Leaf has children')
            ordered.append([address, *node['leaf']])
        else:
            need(set(node) == {'0', '1'}, 'Source tree is not full')
            visit(node['0'], address + '0')
            visit(node['1'], address + '1')
        intervals[address] = (begin, len(ordered))

    visit(trie, '')
    need(ordered == rows, 'Source order is not lexicographic leaf order')
    count = len(rows)

    def enclosing(address, bit, level):
        for i in range(len(address) - 1, -1, -1):
            if address[i] == bit:
                level -= 1
                if level == 0:
                    lo, hi = intervals[address[:i]]
                    return hi % count if bit == '0' else lo
        return 0

    leaves = {p: i for i, (p, _, _) in enumerate(rows)}
    max_depth = max(map(len, leaves))

    def locate(address):
        word = address + '0' * max_depth
        for length in range(1, max_depth + 1):
            prefix = word[:length]
            if prefix in leaves:
                need('1' not in address[length:], 'Stray successor-address one')
                return leaves[prefix]
        raise ValueError('No successor leaf')

    def increment(address):
        if not address:
            return ''
        n = (int(address, 2) + 1) % (1 << len(address))
        return format(n, '0' + str(len(address)) + 'b')

    def cut(address, bit, level):
        positions = [i for i, digit in enumerate(address) if digit == bit]
        return address[:positions[-level]] if len(positions) >= level else ''

    graph, other = [], []
    for i, (address, op, arg) in enumerate(rows):
        after = (i + 1) % count
        if op == 'CI':
            effect = ['increment', arg]
            t, u = [after], [locate(increment(address))]
        elif op == 'CD':
            effect = ['decrement', arg]
            t = [enclosing(address, '0', 1), after]
            u = [locate(increment(cut(address, '0', 1))), locate(increment(address))]
        elif op == 'CB':
            effect = ['identity']
            t = [enclosing(address, '0', arg)]
            u = [locate(increment(cut(address, '0', arg)))]
        elif op == 'CC':
            effect = ['identity']
            t, u = [enclosing(address, '1', arg)], [locate(cut(address, '1', arg))]
        else:
            effect, t, u = ['halt'], [], []
        graph.append([effect, t])
        other.append([effect, u])
    need(graph == other, 'The two source CFG resolvers disagree')
    need(sum(len(t) for effect, t in graph) == 5083, 'Wrong CFG arrow census')
    summary = dict(primitives=count, control_edges=5083, source_sha256=sha(path.read_bytes()),
                   word_sha256=jsha([r[1:] for r in rows]), cfg_sha256=jsha(graph),
                   maximum_depth=max_depth,
                   maximum_zero_run=max(len(s) for p, _, _ in rows for s in p.split('1')),
                   two_cfg_resolvers_agree=True)
    return [r[1:] for r in rows], graph, summary


def pdf_check(directory, plain_bytes, require_extraction):
    pdfs = list(directory.glob('*.pdf'))
    need(len(pdfs) == 1, 'Expected exactly one original PDF in joint_pdf_only')
    command = shutil.which('pdftotext')
    result = dict(pdf=pdfs[0].name, pdf_sha256=sha(pdfs[0].read_bytes()))
    if command is None:
        need(not require_extraction, 'pdftotext is required but unavailable')
        return dict(status='NOT_RERUN_PDFTOTEXT_UNAVAILABLE', **result)
    text = subprocess.run([command, '-layout', str(pdfs[0]), '-'], check=True,
                          stdout=subprocess.PIPE, text=True, encoding='utf-8').stdout
    text = text.split('Complete dense transition table', 1)[1].split('References', 1)[0]
    rows = {}
    for line in text.splitlines():
        for q, zero, one in re.findall(
                r'(?<!\S)(\d+)\s+([01][LR]\d+)\s+([01][LR]\d+)(?!\S)', line):
            q = int(q)
            need(q not in rows, 'Repeated state in PDF appendix')
            rows[q] = [zero, one]
    need(set(rows) == set(range(209)), 'Incomplete PDF transition appendix')
    output = ['#! start 0']
    for q in range(209):
        for bit, action in enumerate(rows[q]):
            output.append(f'{q} {bit} {action[0]} {action[1]} {action[2:]}')
    encoded = ('\n'.join(output) + '\n').encode()
    need(encoded == plain_bytes == (directory / 'u209.tm').read_bytes(),
         'PDF appendix differs from delivered extracted table or Plain table')
    return dict(status='FRESH_PDF_EXTRACTION_BYTE_IDENTICAL', states=209, rows=418,
                extracted_sha256=sha(encoded), **result)


def cycles_to_map(cycles, states):
    rho = {q: q for q in states}
    for cycle in cycles:
        for q, r in zip(cycle, cycle[1:] + cycle[:1]):
            rho[q] = r
    return rho


def compare(root, require_pdf_extraction):
    root = Path(root).resolve()
    directory = root / 'comparison' if (root / 'comparison').is_dir() else root
    need(all((directory / name).is_dir() for name in NAMES), 'Missing snapshot directory')
    dense, canons, summaries, natives, sources = {}, {}, {}, {}, {}
    for name in NAMES:
        path = directory / name / 'u209.tm'
        dense[name] = read_table(path)
        need(dense[name][1] == 209, 'Dense halt is not 209')
        canons[name] = canonical(*dense[name])
        summaries[name] = dict(states=209, rows=418, graph_reachable=209,
                               dense_sha256=sha(path.read_bytes()),
                               canonical_sha256=jsha(canons[name]))
        if name != 'joint_pdf_only':
            native = directory / name / 'u209.native.tm'
            natives[name] = read_table(native)
            native_dense = forced_mapping(natives[name], dense[name])
            need(native_dense['isomorphic'], 'Native/dense disagreement: ' + name)
            summaries[name]['native_sha256'] = sha(native.read_bytes())
            summaries[name]['native_to_dense'] = native_dense['mapping']
            sources[name] = source_graph(directory / name / 'sites.json')
            summaries[name]['source'] = sources[name][2]
    pairs = []
    for a, b in itertools.combinations(NAMES, 2):
        answer = forced_mapping(dense[a], dense[b])
        expected = a in CLASS_A and b in CLASS_A
        need(answer['isomorphic'] == expected, 'Unexpected isomorphism classes')
        need(answer['isomorphic'] == (canons[a] == canons[b]),
             'BFS canonical form and forced-map comparison disagree')
        pairs.append(dict(left=a, right=b, **answer))
    for name, (word, graph, info) in sources.items():
        need(word == sources['joint'][0], 'Primitive word differs: ' + name)
        need(graph == sources['joint'][1], 'Control graph differs: ' + name)
    native_cycles = dict(plain=[[217, 129, 214], [215, 204, 216]],
                         composed=[[217, 129, 204, 214, 216]],
                         compatible_folds=[], joint=[])
    for name, cycles in native_cycles.items():
        answer = forced_mapping(natives[name], natives['joint'])
        states = {q for q, bit in natives[name][0]} | {natives[name][1]}
        need(answer['isomorphic'] and answer['mapping'] == cycles_to_map(cycles, states),
             'Native cycle decomposition differs: ' + name)
    for suffix in ('u209.tm', 'u209.native.tm'):
        need((directory / 'joint' / suffix).read_bytes() ==
             (directory / 'compatible_folds' / suffix).read_bytes(),
             'Joint and Compatible Folds are not byte-identical')
    need((directory / 'joint_pdf_only/u209.tm').read_bytes() ==
         (directory / 'plain/u209.tm').read_bytes(), 'PDF-only and Plain tables differ')
    pdf = pdf_check(directory / 'joint_pdf_only',
                    (directory / 'plain/u209.tm').read_bytes(), require_pdf_extraction)
    return dict(status='ALL_SIX_TWO_ISOMORPHISM_CLASSES_PASS',
                scope='Start, halt, read/write bits, and L/R preserved; no reflection or complement.',
                machines=summaries, pairs=pairs,
                classes=[sorted(CLASS_A), ['compatibility']],
                native_cycles_to_joint=native_cycles,
                all_source_words_equal=True, all_source_cfgs_equal=True,
                joint_folds_native_and_dense_byte_identical=True,
                pdf_only_plain_dense_byte_identical=True, pdf=pdf)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--require-pdf-extraction', action='store_true')
    args = parser.parse_args()
    result = compare(args.root, args.require_pdf_extraction)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], classes=result['classes'],
                         source_words_equal=True, source_cfgs_equal=True,
                         pdf=result['pdf']), indent=2))


if __name__ == '__main__':
    main()
