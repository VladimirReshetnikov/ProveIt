#!/usr/bin/env python3
"""Look for an alternate finite bootstrap of the known prepared252 core.

Only bounded diagnostics are asserted. The exact inherited runtime contract
requires a blank left exterior and a header gap at least40. We compare valid
frames against20000 states of the unchanged register program, allowing a
different register prefix from the standard253 bootstrap.
"""
import argparse
import json
from pathlib import Path
import re
import runtime_fold_search as m


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--steps', type=int, default=5000000)
    ap.add_argument('--rm-steps', type=int, default=20000)
    args = ap.parse_args()
    _, base, env, _ = m.load()
    table = m.FoldedTable(base, '5', '64', (base['64', 0], base['64', 1]))
    body = (m.REPO / 'ZF/m253/coq/tm/Sites253.v').read_text()
    trie = {}
    for code, kind, arg in re.findall(r'\((\d+), (OInc|ODec|OBrk|OCont|OHalt)(?: (\d+))?\)', body):
        path, current = bin(int(code))[3:], trie
        for bit in path[:-1]:
            current = current.setdefault(int(bit), {})
        current[int(path[-1])] = kind, int(arg) if arg else None
    def walk(read):
        current, path, index = trie, '', 0
        while isinstance(current, dict):
            bit = read(index)
            path += str(bit)
            current = current[bit]
            index += 1
        return path, current
    regs, path, references = [0] * 9, '', {}
    regs[6] = 2  # physical position of nextproof
    for rm_elapsed in range(args.rm_steps):
        references[path.rstrip('0'), tuple(regs)] = rm_elapsed
        full_path, (kind, argument) = walk(lambda j: int(path[j]) if j < len(path) else 0)
        if kind == 'OInc':
            regs[argument] += 1
            path = env['inc'](full_path) or ''
        elif kind == 'ODec':
            if regs[argument]:
                regs[argument] -= 1
                path = env['inc'](full_path) or ''
            else:
                path = env['inc'](env['strip']('0', 1, full_path)) or ''
        elif kind == 'OBrk':
            path = env['inc'](env['strip']('0', argument, full_path)) or ''
        elif kind == 'OCont':
            path = env['strip']('1', argument, full_path)
        else:
            break
    state, head, ones = '64', 0, set()
    visits, valid, maximum_gap, best, matched = 0, 0, -1, None, None
    for elapsed in range(args.steps + 1):
        if state == '96':
            visits += 1
            if head - 1 in ones and all(x >= head - 1 for x in ones):
                full_path, _ = walk(lambda j: int(head + j in ones))
                right_ones = [x for x in ones if x >= head + len(full_path)]
                if right_ones:
                    header = min(right_ones)
                    values, index, last = [], header + 1, max(ones)
                    while index < last:
                        if index in ones:
                            break
                        index += 1
                        value = -1
                        while index in ones:
                            value += 1
                            index += 1
                        if value < 0:
                            break
                        values.append(value)
                    if index > last and len(values) >= 9:
                        valid += 1
                        gap = header - head
                        frame = {'steps': elapsed, 'head': head, 'path': full_path,
                                 'gap': gap, 'physical_regs': values[:9], 'spares': len(values) - 9}
                        if gap > maximum_gap:
                            maximum_gap, best = gap, frame
                        key = full_path.rstrip('0'), tuple(values[:9])
                        if gap >= 40 and key in references:
                            matched = frame | {'RM_steps': references[key]}
                            break
        if state == '254' or elapsed == args.steps:
            break
        write, direction, target = table[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        state = target
    report = {'steps_checked': elapsed, 'all_dispatch_visits': visits,
              'frames_with_valid_tape_shape': valid, 'max_gap': maximum_gap,
              'best_frame': best, 'matched_RM_prefix': matched,
              'RM_prefix_states_checked': len(references),
              'not_a_nonhalting_or_inequivalence_proof': True}
    path = Path(__file__).resolve().parent / 'prepared252-frame-search.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
