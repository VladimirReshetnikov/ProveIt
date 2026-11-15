#!/usr/bin/env python3
"""Resolve all source targets twice, independently of the construction compiler."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'verification' / 'vendor'))
import source_language as source

MAP = {'inc':'CI', 'dec':'CD', 'breakTo':'CB', 'continueTo':'CC', 'halt':'CH'}
NAMES = {'identity':'jump', 'increment':'inc', 'decrement':'dec', 'halt':'halt'}
VARIANTS = ['PA194LC', 'PA194LC_A', 'PA194LC_B', 'PA194LC_C']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def resolved(directory):
    sites = json.loads((directory / 'sites.json').read_text())
    mapped = [[p, MAP[op], arg] for p, op, arg in sites]
    graph, _ = source.graph_arithmetic(mapped)
    assert graph == source.graph_intervals(mapped)
    instructions = [[NAMES[e[0]]] + e[1:] + targets for e, targets in graph]
    assert instructions == json.loads((directory / 'instructions.json').read_text())
    return sites, instructions

def main():
    assert __debug__
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, default=ROOT/'verification/source_binding.json')
    args = ap.parse_args()
    baseline = ROOT / 'reference' / 'primary'
    old_sites, old_instructions = resolved(baseline)
    assert sha(baseline/'machine.tm') == '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
    results = []
    for name in VARIANTS:
        directory = ROOT / 'machines' / name
        sites, instructions = resolved(directory)
        assert instructions == old_instructions and len(instructions) == 3673
        results.append(dict(name=name, source_sites=len(instructions),
            all_instructions_and_targets_equal_primary=True,
            two_independent_resolvers_agree=True,
            changed_source_addresses=sum(a[0] != b[0] for a,b in zip(old_sites,sites)),
            maximum_address_length=max(len(s[0]) for s in sites),
            instructions_sha256=sha(directory/'instructions.json'),
            sites_sha256=sha(directory/'sites.json'),
            dense_sha256=sha(directory/'machine.tm')))
    result = dict(status='PASS', primary_dense_sha256=sha(baseline/'machine.tm'),
        scope='Exact resolved source graphs; physical contracts and arithmetic soundness are separate checks.',
        results=results)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
