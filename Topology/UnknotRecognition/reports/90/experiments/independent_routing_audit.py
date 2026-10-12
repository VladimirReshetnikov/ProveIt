"""Reproduce independent vertex-label and concrete source-coloring audits.

The finite reference expands the original source and every binary coloring run
only for deliberately small exponents.  It compares exact original cut and mark
addresses, not merely the reported decision.  No production files are modified.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'code'), str(ROOT / 'experiments')]

from pattern_kernel.core import Tile, Block, expand
from routed_patterns.core import build_kernel, solve
from routed_patterns.verify import reconstruct, verify_result, verify_source_witness
from routing_audit import random_aligned
from routing_families import star_triangle, connected_context, routed_beads


def relabel(tile, rng, coordinates=None, reverse=False):
    permutation = list(range(tile.n))
    rng.shuffle(permutation)
    edges = [(permutation[a], permutation[b]) if rng.randrange(2)
             else (permutation[b], permutation[a]) for a, b in tile.edges]
    rng.shuffle(edges)
    coordinates = coordinates or list(range(tile.width))
    left = tuple(permutation[tile.left[i]] for i in coordinates)
    right = tuple(permutation[tile.right[i]] for i in coordinates)
    return Tile(tile.n, tuple(edges), right if reverse else left,
                left if reverse else right)


def source_components(tile):
    """Independent edge-set flood fill, used only to decode finite run words."""
    remaining = set(range(tile.n))
    groups = []
    while remaining:
        vertices = {min(remaining)}
        while True:
            larger = set(vertices)
            for a, b in tile.edges:
                if a in vertices or b in vertices:
                    larger.update((a, b))
            if larger == vertices:
                break
            vertices = larger
        remaining -= vertices
        left = tuple(i for i, v in enumerate(tile.left) if v in vertices)
        right = tuple(i for i, v in enumerate(tile.right) if v in vertices)
        groups.append((vertices, left, right))
    groups.sort(key=lambda group: group[1])
    left_parts = [group[1] for group in groups]
    permutation = [left_parts.index(group[2]) for group in groups]
    return groups, permutation


def expand_source_coloring(chain, witness):
    """Expand the claimed coloring, then independently test the actual source."""
    all_masks = []
    for block, record in zip(chain, witness['blocks']):
        tile = block.tile
        if record['kind'] == 'literal':
            all_masks.append([int(value, 16) for value in record['colors']])
            continue
        groups, permutation = source_components(tile)
        masks = [0] * block.copies
        covered = [set() for _ in range(block.copies)]
        for start, path in enumerate(record['paths']):
            offset = 0
            phase = start
            for segment in path['segments']:
                for _ in range(int(segment['repeat'], 16)):
                    for word_mask in segment['word']:
                        vertices = groups[phase][0]
                        if covered[offset] & vertices:
                            raise AssertionError('overlapping original component occurrence')
                        covered[offset] |= vertices
                        masks[offset] |= int(word_mask, 16)
                        offset += 1
                        phase = permutation[phase]
            if offset != block.copies:
                raise AssertionError('wrong expanded source exponent')
        if not all(vertices == set(range(tile.n)) for vertices in covered):
            raise AssertionError('source occurrence has uncolored vertices')
        all_masks.append(masks)

    graph, maps = expand(chain)
    colors = [None] * graph.n
    for block_masks, block_maps in zip(all_masks, maps):
        for mask, image in zip(block_masks, block_maps):
            for local, vertex in enumerate(image):
                color = (mask >> local) & 1
                if colors[vertex] is not None and colors[vertex] != color:
                    raise AssertionError('concrete original source seam disagrees')
                colors[vertex] = color
    if any(color is None for color in colors):
        raise AssertionError('expanded source vertex is uncolored')

    expected = []
    for bi, (block, block_masks) in enumerate(zip(chain, all_masks)):
        for copy, mask in enumerate(block_masks):
            for edge, (a, b) in enumerate(block.tile.edges):
                if ((mask >> a) ^ (mask >> b)) & 1:
                    expected.append((bi, copy, edge))
    checked = verify_source_witness(chain, witness)
    actual = sorted((address['block'], int(address['copy'], 16), address['edge'])
                    for address in checked['crossings'])
    if actual != expected:
        raise AssertionError('original cut-edge addresses differ')
    if len(expected) != sum(colors[a] != colors[b] for a, b in graph.edges):
        raise AssertionError('original cut cost differs')
    for color, address in enumerate(checked['anchors']):
        bi, copy, edge = address['block'], int(address['copy'], 16), address['edge']
        a, b = chain[bi].tile.edges[edge]
        mask = all_masks[bi][copy]
        if ((mask >> a) & 1) != color or ((mask >> b) & 1) != color:
            raise AssertionError('original monochromatic anchor differs')
    return len(graph.edges), len(expected)


def main():
    seed = 19720615
    rng = random.Random(seed)
    reconstruction_cases = 300
    for trial in range(reconstruction_cases):
        width = 1 + rng.randrange(7)
        chain = tuple(
            Block(relabel(random_aligned(rng, width), rng),
                  rng.choice([1, 2, 3, 4, 5, 17, 10**20 + 3]))
            for _ in range(1 + rng.randrange(4)))
        kernel, plans, _ = build_kernel(chain)
        if reconstruct(chain, plans) != kernel:
            raise AssertionError(('finite canonical labels differ', trial))

    source_cases = 120
    negative_cases = 0
    expanded_edges = 0
    maximum_cut_size = 0
    for trial in range(source_cases):
        coordinates = list(range(3))
        rng.shuffle(coordinates)
        reverse = bool(rng.randrange(2))
        if trial % 2:
            base = [star_triangle(), connected_context()]
        else:
            permutations = list(itertools.permutations(range(3)))
            base = [routed_beads(rng.choice(permutations)),
                    routed_beads(rng.choice(permutations))]
        chain = tuple(
            Block(relabel(rng.choice(base), rng, coordinates, reverse),
                  1 + rng.randrange(70))
            for _ in range(1 + rng.randrange(3)))
        result = solve(chain)
        if not verify_result(chain, result):
            raise AssertionError(('certificate replay failed', trial))
        if result['graph_proof']['verdict'] == 'LOW_CYCLIC_CUT':
            edges, cut_size = expand_source_coloring(chain, result['source_witness'])
            negative_cases += 1
            expanded_edges += edges
            maximum_cut_size = max(maximum_cut_size, cut_size)

    report = {
        'all_passed': True,
        'seed': seed,
        'canonical_reconstruction_chains': reconstruction_cases,
        'canonical_reconstruction_width_range': [1, 7],
        'largest_reconstruction_exponent': str(10**20 + 3),
        'cubic_source_chains_checked': source_cases,
        'negative_source_colorings_expanded': negative_cases,
        'other_verified_verdicts': source_cases - negative_cases,
        'actual_source_edge_occurrences_checked': expanded_edges,
        'maximum_checked_cut_size': maximum_cut_size,
        'finite_source_exponent_range': [1, 70],
        'checks': ['shuffled local vertex IDs and edge order/direction',
                   'whole-tile reversal and simultaneous port-coordinate permutation',
                   'fresh-copy quotient labels equal incremental producer labels',
                   'complete original component coverage per source copy',
                   'every concrete original source seam has consistent colors',
                   'exact cut-edge addresses and both original edge-mark witnesses'],
    }
    text = json.dumps(report, indent=2) + '\n'
    (ROOT / 'results' / 'independent_routing_audit.json').write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
