#!/usr/bin/env python3
"""Compare exact deterministic binary TMs, without importing proposal code.

Input: the snapshot subdirectory shipped alongside this script.
Graph isomorphism is rooted, start/halt/read/write/move preserving.
The BFS input words are graph-edge labels, not tape execution traces.
"""
from collections import deque
from itertools import combinations
from pathlib import Path
import hashlib
import json
import re


ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, direction, r = line.split()
        q, b, w, r = map(int, (q, b, w, r))
        require((q, b) not in table, 'Duplicate row')
        table[q, b] = w, direction, r
    states = {q for q, _ in table}
    require(states == set(range(209)), 'Working labels')
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Totality')
    require(all(w in (0, 1) and d in ('L', 'R') and r in states | {209}
                for w, d, r in table.values()), 'Invalid transition')
    reached, pending = {0}, [0]
    while pending:
        state = pending.pop()
        if state == 209:
            continue
        for bit in (0, 1):
            target = table[state, bit][2]
            if target not in reached:
                reached.add(target)
                pending.append(target)
    require(reached == states | {209}, 'Not all vertices graph-reachable')
    return table


def rooted_isomorphism(left, right):
    forward, reverse = {0: 0, 209: 209}, {0: 0, 209: 209}
    pending, words = deque([0]), {0: ''}
    while pending:
        q = pending.popleft()
        r = forward[q]
        if q == 209:
            continue
        for bit in (0, 1):
            a, b = left[q, bit], right[r, bit]
            witness = {'input_word': words[q] + str(bit),
                       'left_state': q, 'right_state': r,
                       'left_transition': a, 'right_transition': b}
            if a[:2] != b[:2]:
                return False, {'kind': 'action_mismatch', **witness}
            x, y = a[2], b[2]
            if x in forward and forward[x] != y:
                return False, {'kind': 'forward_map_conflict',
                               'previous_target': forward[x], **witness}
            if y in reverse and reverse[y] != x:
                return False, {'kind': 'inverse_map_conflict',
                               'previous_source': reverse[y], **witness}
            if x not in forward:
                forward[x], reverse[y] = y, x
                words[x] = words[q] + str(bit)
                pending.append(x)
    require(len(forward) == 210, 'Incomplete isomorphism')
    for (q, bit), (w, d, r) in left.items():
        require(right[forward[q], bit] == (w, d, forward[r]), 'Map not isomorphism')
    return True, {'mapping': forward}


def source_graph(sites):
    """Resolve controls using lexicographic prefix intervals and ancestor cuts."""
    words = [row[0] for row in sites]
    require(words == sorted(set(words)), 'Source leaf ordering')
    spans = {}
    for i, word in enumerate(words):
        for length in range(len(word) + 1):
            prefix = word[:length]
            if prefix in spans:
                spans[prefix][1] = i + 1
            else:
                spans[prefix] = [i, i + 1]
    leaf_set = set(words)
    for prefix in spans:
        if prefix in leaf_set:
            require(prefix + '0' not in spans and prefix + '1' not in spans,
                    'Leaf is also an internal prefix')
        else:
            require(prefix + '0' in spans and prefix + '1' in spans, 'Tree not full')

    def control(word, bit, count):
        occurrences = [i for i, char in enumerate(word) if char == bit]
        if len(occurrences) < count:
            return 0
        prefix = word[:occurrences[-count]]
        return spans[prefix][1 if bit == '0' else 0] % len(sites)

    result = []
    for i, (word, op, arg) in enumerate(sites):
        following = (i + 1) % len(sites)
        if op == 'CI':
            successors = [following]
        elif op == 'CD':
            successors = [control(word, '0', 1), following]
        elif op == 'CB':
            successors = [control(word, '0', arg)]
        elif op == 'CC':
            successors = [control(word, '1', arg)]
        elif op == 'CH':
            successors = []
        else:
            raise ValueError('Unknown instruction')
        result.append([op, arg, successors])
    return result


def main():
    metadata = json.loads((ROOT / 'snapshots/provenance.json').read_text())
    for record in metadata['files']:
        path = ROOT / 'snapshots' / record['file']
        require(hashlib.sha256(path.read_bytes()).hexdigest() == record['sha256'],
                'Changed snapshot: ' + record['file'])
    names = ['Plain', 'Compatibility', 'Compatible_Folds', 'Composed', 'Joint', 'Joint_PDF']
    tables = {name: load_table(ROOT / 'snapshots' / (name + '.tm')) for name in names}
    sources = {name: json.loads((ROOT / 'snapshots' / (name + '.sites.json')).read_text())
               for name in names[:-1]}
    graphs = {name: source_graph(sites) for name, sites in sources.items()}
    require(all(graph == graphs['Plain'] for graph in graphs.values()), 'Source CFG differs')
    require(sum(len(row[2]) for row in graphs['Plain']) == 5083, 'Control-edge census')
    pairs = []
    for left, right in combinations(names, 2):
        isomorphic, witness = rooted_isomorphism(tables[left], tables[right])
        pairs.append({'left': left, 'right': right,
                      'literal_equal': tables[left] == tables[right],
                      'row_differences': sum(tables[left][key] != tables[right][key]
                                             for key in tables[left]),
                      'rooted_labeled_isomorphic': isomorphic, 'witness': witness})
    result = {'status': 'PASS', 'snapshot': metadata['commit'],
              'tables_checked': len(tables), 'working_states_each': 209,
              'rows_each': 418, 'source_primitives_each': 3909,
              'source_edges_each': 5083, 'all_source_cfgs_equal': True,
              'rooted_isomorphism_classes': [
                  ['Plain', 'Compatible_Folds', 'Composed', 'Joint', 'Joint_PDF'],
                  ['Compatibility']], 'pairs': pairs}
    (ROOT / 'independent_comparison.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: six table presentations, two isomorphism classes, common source CFG.')


if __name__ == '__main__':
    main()
