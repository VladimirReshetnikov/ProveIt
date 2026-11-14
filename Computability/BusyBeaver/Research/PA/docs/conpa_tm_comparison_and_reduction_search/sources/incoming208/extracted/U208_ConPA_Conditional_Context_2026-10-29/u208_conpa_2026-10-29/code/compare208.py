#!/usr/bin/env python3
"""Independent rooted graph comparison of two native-label U208 candidates."""
from collections import deque
from pathlib import Path
import argparse
import hashlib
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        need((q, bit) not in table, 'Duplicate row')
        table[q, bit] = write, direction, target
    states = {q for q, _ in table}
    need(len(states) == 208 and len(table) == 416, 'U208 count')
    need(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Total table')
    need(all(w in (0, 1) and d in ('L', 'R') and r in states | {254}
             for w, d, r in table.values()), 'Invalid row')
    return table


def walk(table, word):
    state = 0
    for bit in word:
        state = table[state, int(bit)][2]
    return state


def compare(left, right):
    forward, reverse = {0: 0, 254: 254}, {0: 0, 254: 254}
    queue, paths_left, paths_right = deque([0]), {0: ''}, {0: ''}
    while queue:
        q = queue.popleft()
        if q == 254:
            continue
        r = forward[q]
        for bit in (0, 1):
            a, b = left[q, bit], right[r, bit]
            word = paths_left[q] + str(bit)
            if a[:2] != b[:2]:
                return {'isomorphic': False, 'kind': 'action_mismatch',
                        'word': word, 'left_action': a[:2], 'right_action': b[:2]}
            x, y = a[2], b[2]
            if x in forward and forward[x] != y:
                earlier = paths_left[x]
                need(walk(left, earlier) == walk(left, word), 'Bad left witness')
                need(walk(right, earlier) != walk(right, word), 'Bad right witness')
                return {'isomorphic': False, 'kind': 'forward_identity_conflict',
                        'earlier_word': earlier, 'new_word': word,
                        'left_endpoints': [walk(left, earlier), walk(left, word)],
                        'right_endpoints': [walk(right, earlier), walk(right, word)]}
            if y in reverse and reverse[y] != x:
                earlier = paths_right[y]
                need(walk(right, earlier) == walk(right, word), 'Bad right witness')
                need(walk(left, earlier) != walk(left, word), 'Bad left witness')
                return {'isomorphic': False, 'kind': 'reverse_identity_conflict',
                        'earlier_word': earlier, 'new_word': word,
                        'left_endpoints': [walk(left, earlier), walk(left, word)],
                        'right_endpoints': [walk(right, earlier), walk(right, word)]}
            if x not in forward:
                forward[x], reverse[y] = y, x
                paths_left[x], paths_right[y] = word, word
                queue.append(x)
    return {'isomorphic': True, 'mapping': forward}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('left', type=Path)
    parser.add_argument('right', type=Path)
    parser.add_argument('--output', type=Path, default=Path('comparison208.json'))
    args = parser.parse_args()
    result = compare(read(args.left), read(args.right))
    result.update({'left_sha256': hashlib.sha256(args.left.read_bytes()).hexdigest(),
                   'right_sha256': hashlib.sha256(args.right.read_bytes()).hexdigest(),
                   'scope': 'Rooted start/halt/read/write/direction preserving graph isomorphism; graph words are not tape histories.'})
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
