#!/usr/bin/env python3
"""Independent finite certificate for the boundary source and tape interface.

Unlike the inherited tree-walking checker, this program decodes a source path
by locating its dyadic interval, using integer arithmetic and binary search.
It replays rotations as simultaneous rewrites of path prefixes. It checks
complete control graphs, not runs or a sampled set of register assignments.

Python standard library only. All checks remain active under Python -O.
"""
from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

WIDTH = 64
BASELINE_SHA = '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
CANDIDATE_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
ROTATIONS_SHA = '73b4688ec38ecdd250c34752c57c180fcc0d03042f6383e9d686e81b1e8e2063'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def padded_integer(word):
    require(isinstance(word, str) and set(word) <= {'0', '1'}, 'Invalid binary word')
    require(len(word) <= WIDTH, 'Word exceeds exact common dyadic width')
    return (int(word, 2) if word else 0) << (WIDTH - len(word))


def increment(word):
    if not word:
        return ''
    length = len(word)
    result = ((int(word, 2) + 1) % (1 << length))
    return format(result, f'0{length}b')


def strip(word, digit, count):
    require(type(count) is int and count >= 0, 'Invalid strip count')
    if count == 0:
        return word
    locations = [index for index, value in enumerate(word) if value == digit]
    return word[:locations[-count]] if count <= len(locations) else ''


class Source:
    def __init__(self, sites):
        require(type(sites) is list and len(sites) == 6455, 'Wrong leaf count')
        require(sites == sorted(sites), 'Source must be ordered by leaf path')
        seen, self.starts, self.ends = set(), [], []
        for row in sites:
            require(type(row) is list and len(row) == 3, 'Malformed source row')
            word, operation, argument = row
            require(bool(word) and word not in seen, 'Empty or duplicate leaf path')
            require(operation in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Unknown operation')
            if operation == 'CH':
                require(argument is None, 'Halt operand must be null')
            else:
                require(type(argument) is int and argument >= 0, 'Invalid natural operand')
                if operation in ('CI', 'CD'):
                    require(argument < 9, 'Primary register out of range')
            start = padded_integer(word)
            end = start + (1 << (WIDTH - len(word)))
            require(start == (self.ends[-1] if self.ends else 0), 'Dyadic leaves do not partition the path space')
            self.starts.append(start)
            self.ends.append(end)
            seen.add(word)
        require(self.ends[-1] == 1 << WIDTH, 'Dyadic path partition is incomplete')
        self.sites = sites

    def locate(self, word):
        value = padded_integer(word)
        index = bisect_right(self.starts, value) - 1
        require(0 <= index < len(self.sites) and value < self.ends[index], 'Bad dyadic decoder')
        return index

    def successors(self, word, operation, argument):
        if operation == 'CI':
            return [increment(word)]
        if operation == 'CD':
            return [increment(word), increment(strip(word, '0', 1))]
        if operation == 'CB':
            return [increment(strip(word, '0', argument))]
        if operation == 'CC':
            return [strip(word, '1', argument)]
        return []

    def graph_and_interface(self):
        graph = []
        coverage = Counter()
        exact_frame_checks = 0
        for row in self.sites:
            word, operation, argument = row
            require(self.locate(word) == len(graph), 'Leaf identity mismatch')
            words = self.successors(*row)
            targets = [self.locate(successor) for successor in words]
            for successor, target in zip(words, targets):
                # Equal padded integers with both lengths <=64 prove equality
                # after ANY amount of zero padding, not just within 64 cells.
                require(padded_integer(successor) == self.starts[target],
                        f'Nonzero discarded successor tail at {row}')
                # Equal finite support of the path's one bits is precisely
                # equal whole tape, since marker/header/register file agree.
                successor_ones = {j for j, b in enumerate(successor) if b == '1'}
                leaf_ones = {j for j, b in enumerate(self.sites[target][0]) if b == '1'}
                require(successor_ones == leaf_ones, 'Clean-frame support mismatch')
                exact_frame_checks += 1
            if operation in ('CI', 'CD'):
                graph.append([operation, argument, *targets])
            elif operation in ('CB', 'CC'):
                graph.append(['J', *targets])
            else:
                graph.append(['H'])
            coverage[operation] += len(words)
        require(self.locate('') == 0, 'Root must locate first leaf')
        require(self.starts[0] == padded_integer(''), 'Root clean frame mismatch')
        require(all(b == '0' for b in self.sites[0][0]), 'First leaf is not zero-only')
        return graph, dict(coverage), exact_frame_checks

    def metrics(self):
        # Bottom-up interning reconstructs a DAG independently of the
        # inherited recursive tree constructor.
        names = {}
        nodes = {}
        for path, op, arg in self.sites:
            key = ('leaf', op, arg)
            if key not in names:
                names[key] = len(names)
            nodes[path] = names[key]
        prefixes = {p[:k] for p, _, _ in self.sites for k in range(len(p))}
        for prefix in sorted(prefixes, key=len, reverse=True):
            require(prefix+'0' in nodes and prefix+'1' in nodes, 'Tree is not full binary')
            key = ('pair', nodes[prefix+'0'], nodes[prefix+'1'])
            if key not in names:
                names[key] = len(names)
            nodes[prefix] = names[key]
        require('' in nodes, 'Missing root')
        return dict(leaves=len(self.sites), dag_nodes=len(names),
                    leaf_kinds=len(set((op, arg) for _, op, arg in self.sites)),
                    maximum_path_length=max(len(p) for p, _, _ in self.sites),
                    maximum_zero_run=max(len(run) for p, _, _ in self.sites for run in p.split('1')))


def rotate_paths(sites, stage):
    paths = stage['paths']
    require(len(paths) == len(set(paths)), 'Repeated rotation target')
    require(all(isinstance(p, str) and set(p) <= {'0','1'} for p in paths), 'Invalid rotation path')
    require(not any(p != q and q.startswith(p) for p in paths for q in paths), 'Rotation targets overlap')
    direction = stage['direction']
    require(direction in ('left','right'), 'Unknown rotation direction')
    rules = [('0', '00'), ('10', '01'), ('11', '1')] if direction == 'left' else [('00', '0'), ('01', '10'), ('1', '11')]
    used = Counter()
    result = []
    for path, operation, argument in sites:
        output = path
        for prefix in paths:
            if path.startswith(prefix):
                suffix = path[len(prefix):]
                matches = [(old, new) for old, new in rules if suffix.startswith(old)]
                require(len(matches) == 1, 'Rotation does not have three nonempty child subtrees')
                old, new = matches[0]
                output = prefix + new + suffix[len(old):]
                used[prefix, old] += 1
                break
        result.append([output, operation, argument])
    require(all(used[prefix, old] > 0 for prefix in paths for old, _ in rules), 'Missing rotation child subtree')
    require(result == sorted(result), 'Rotation failed to preserve leaf order')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--rotations', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    for path, digest in [(args.baseline, BASELINE_SHA), (args.rotations, ROTATIONS_SHA), (args.candidate, CANDIDATE_SHA)]:
        require(sha256(path.read_bytes()).hexdigest() == digest, f'Wrong pinned bytes: {path}')
    cert = json.loads(args.rotations.read_text())
    require(cert['format'] == 'busy-beaver-source-rotation-certificate-v1', 'Invalid certificate format')
    require(cert['baseline_sha256'] == BASELINE_SHA, 'Certificate baseline mismatch')
    source = Source(json.loads(args.baseline.read_text()))
    graph, coverage, frames = source.graph_and_interface()
    require(len(graph) == 6455 and frames == 8385, 'Wrong graph census')
    require(sum(entry == ['H'] for entry in graph) == 1, 'Wrong halt census')
    initial = source.metrics()
    word = [row[1:] for row in source.sites]
    stages = []
    for number, stage in enumerate(cert['steps'], 1):
        require(stage['number'] == number, 'Invalid stage order')
        source = Source(rotate_paths(source.sites, stage))
        require([row[1:] for row in source.sites] == word, 'Instruction word changed')
        new_graph, new_coverage, new_frames = source.graph_and_interface()
        require(new_graph == graph, f'Complete graph mismatch after stage {number}')
        require(new_coverage == coverage and new_frames == frames, 'Guard coverage mismatch')
        stages.append(dict(stage=number, rotations=len(stage['paths']), **source.metrics()))
    require(source.sites == json.loads(args.candidate.read_text()), 'Final literal source mismatch')
    require(len(stages) == 13 and sum(s['rotations'] for s in stages) == 25, 'Wrong rotation census')
    require(source.metrics() == dict(leaves=6455, dag_nodes=224, leaf_kinds=23, maximum_path_length=48, maximum_zero_run=6), 'Wrong final source metrics')
    result = dict(status='PASS_INDEPENDENT_DYADIC_SOURCE_AND_FRAME_INTERFACE',
                  method='Dyadic integer partition, binary search, and path-prefix substitution',
                  baseline_sha256=BASELINE_SHA, candidate_sha256=CANDIDATE_SHA,
                  rotation_certificate_sha256=ROTATIONS_SHA,
                  normalized_control_graph_sha256=sha256(json.dumps(graph,separators=(',',':')).encode()).hexdigest(),
                  guarded_edges_per_source=frames, halt_descriptors_per_source=1,
                  successor_frame_equalities_per_source=frames,
                  sources_checked_including_baseline=len(stages)+1,
                  infinite_zero_padding_identity_checked=True,
                  empty_pointer_frame_identity_checked=True,
                  initial=initial, final=source.metrics(), stages=stages,
                  scope='Finite complete structural certificate proving unbounded register-source bisimulation and clean-frame composition; no TM execution, register sample, or kernel claim.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'stages'}, indent=2))


if __name__ == '__main__':
    main()
