#!/usr/bin/env python3
"""Independently check the retained exact-word grammar and its declared cost.

This checks the emitted canonical-substring grammar, not the optimizer's
search coverage and not a general binary compiler theorem.
"""
import argparse
import json
from pathlib import Path


def check(directory, baseline):
    retained = list(map(int, (directory / 'best.txt').read_text().split()))
    declared, count, *splits = retained
    assert len(splits) == count
    lines = (directory / 'input.txt').read_text().splitlines()
    n, root, base, fixed_framework, fixed_depth, root_extra = map(int, lines[0].split())
    assert count == n == len(lines) - 1
    descriptions = json.loads((directory / 'strings.json').read_text())
    words = descriptions['strings']
    assert len(words) == n and descriptions['root'] == root
    expected = json.loads(baseline.read_text())['primitive_word']
    assert words[root] == expected
    used, memo = set(), {}
    maximum = fixed_depth

    def visit(index):
        nonlocal maximum
        if index in memo:
            return memo[index]
        fields = list(map(int, lines[index + 1].split()))
        length, fixed, depth, initial_split = fields[:4]
        assert length == len(words[index])
        assert len(fields) == 4 + 2 * (length - 1)
        if fixed:
            assert str(index) in descriptions['available']
            memo[index] = depth
            return depth
        split = splits[index]
        assert 1 <= split < length
        left, right = fields[4 + 2 * (split - 1):6 + 2 * (split - 1)]
        assert len(words[left]) == split
        assert words[left] + words[right] == words[index]
        assert len(words[left]) < length and len(words[right]) < length
        used.add(index)
        answer = visit(left) + 1
        visit(right)
        maximum = max(maximum, answer)
        memo[index] = answer
        return answer

    root_depth = visit(root)
    maximum = max(maximum, root_depth + root_extra)
    states = base + len(used) + fixed_framework + maximum
    assert states == declared
    return {'exact_primitive_word_preserved': True,
            'distinct_substrings': n, 'primitive_word_length': len(expected),
            'new_reachable_grammar_nodes': len(used),
            'decision_nodes': base + len(used),
            'dispatcher_depth': maximum,
            'framework_states': fixed_framework + maximum,
            'working_states': states,
            'binary_compiler_or_consistency_endpoint_proved': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('baseline', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check(args.directory, args.baseline)
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
