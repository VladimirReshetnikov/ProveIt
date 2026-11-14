#!/usr/bin/env python3
"""Optionally regenerate the frozen symbolic context sample.

This optional command uses the adjacent release's construction/vendor compiler
and symbolic runtime. The default search.py does not need either module.
It never imports the working-tree search_compose experiment.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import importlib
import json
import sys

HERE = Path(__file__).resolve().parent


def tuples(value):
    if isinstance(value, list):
        return tuple(tuples(item) for item in value)
    if isinstance(value, dict):
        return {key: tuples(item) for key, item in value.items()}
    return value


def bits(segments, width):
    """Original observer's extraction of a fixed known-bit prefix."""
    out = []
    for segment in segments:
        if segment[0] == 'b':
            out.append(segment[1])
        elif segment[0] == 'r':
            out += [segment[1]] * min(width - len(out), segment[3])
            if len(out) < width and segment[2] > 0:
                return ''.join(map(str, out)) + '?'
        else:
            return ''.join(map(str, out)) + '?'
        if len(out) >= width:
            break
    return ''.join(map(str, out))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--construction', type=Path,
                        default=HERE.parent.parent / 'construction',
                        help='Final bundle construction directory containing vendor/.')
    parser.add_argument('--output', type=Path, default=HERE / 'regenerated')
    parser.add_argument('--source-only', action='store_true',
                        help='Check frozen source bindings and contract count, without running contracts.')
    args = parser.parse_args()
    if not __debug__:
        parser.error('Do not run Python with -O.')
    from search import read_table, verify_manifest
    verify_manifest()
    provenance = json.loads((HERE / 'PROVENANCE.json').read_text())
    vendor = args.construction.resolve() / 'vendor'
    for filename, key in [('compiler.py', 'compiler_sha256'),
                          ('symbolic_runtime.py', 'symbolic_runtime_sha256')]:
        path = vendor / filename
        if not path.is_file():
            parser.error(f'Missing {filename}; pass --construction with the release construction directory.')
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        assert digest == provenance['context_generation'][key], ('different vendor input', filename)
    sys.path.insert(0, str(vendor))
    compiler = importlib.import_module('compiler')
    compiler.ROOT = args.construction.resolve() / 'inputs'
    nodes = tuples(json.loads((HERE / 'data/nodes.json').read_text()))
    compiler.raw_nodes = lambda: nodes
    grammar = compiler.read_grammar(HERE / 'data/grammar.json')
    sites, instructions, contracts = compiler.source(grammar)
    assert json.loads(json.dumps(sites)) == json.loads((HERE / 'data/sites.json').read_text())
    assert json.loads(json.dumps(instructions)) == json.loads((HERE / 'data/instructions.json').read_text())
    assert len(contracts) == 4812
    receipt = {'source_binding': 'exact', 'source_sites': len(sites),
               'source_outcomes': len(contracts), 'kernel_checked': False}
    args.output.mkdir(parents=True, exist_ok=True)
    if args.source_only:
        receipt['context_regeneration'] = 'not requested'
    else:
        contexts = collections.defaultdict(set)

        def observe(state):
            q, on_left, left, right = state
            if q in (41, 99, 330, 331) and not on_left:
                contexts[q].add((bits(left, 8)[::-1], bits(right, 3)))

        rows = read_table(HERE / 'data/raw.native.tm')
        validation = compiler.validate(rows, contracts, observe=observe)
        assert validation == provenance['context_generation']['symbolic_validation']
        result = {str(q): sorted(samples) for q, samples in contexts.items()}
        result = json.loads(json.dumps(result))
        assert result == json.loads((HERE / 'data/contexts.json').read_text())
        (args.output / 'contexts.json').write_text(json.dumps(result, indent=2) + '\n')
        receipt['context_regeneration'] = 'exact match'
        receipt['validation'] = validation
    (args.output / 'context_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
