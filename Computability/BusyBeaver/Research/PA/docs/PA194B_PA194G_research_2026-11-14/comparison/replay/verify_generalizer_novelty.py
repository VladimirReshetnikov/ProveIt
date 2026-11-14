#!/usr/bin/env python3
"""Fast exact graph-novelty certificate for PA194G against the pinned corpus.

PA194G has 88 working controls of indegree one; none of the 82 prior
194-control graph representatives does. Indegree counts both read-symbol
edges, including repeated edges, and ignores read/write/move labels. This
invariant is preserved by arbitrary state renaming, root choice, reflection,
symbol exchange, and changes to terminal-edge write/move actions. It proves
table nonidentity, not correctness, calibration, or materiality of a change.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
from literal_inventory import parse_table, canonical

HERE = Path(__file__).resolve().parent


def fail_unless(condition, message):
    if not condition:
        raise ValueError(message)


def graph_statistics(data):
    rows, states, halt = data
    incoming = collections.Counter(target for write, move, target in rows.values())
    histogram = dict(sorted(collections.Counter(incoming[q] for q in states).items()))
    return dict(working_indegree_histogram=histogram,
                working_indegree_one=histogram.get(1, 0),
                halt_indegree=incoming[halt],
                self_loop_edges=sum(target == q for (q, bit), (write, move, target)
                                    in rows.items()))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--frontier', type=Path, default=HERE / 'frontier_tables')
    ap.add_argument('--manifest', type=Path, default=HERE / 'table_manifest.json')
    ap.add_argument('--output', type=Path,
                    default=Path.cwd() / 'generalizer-novelty-replay.json')
    args = ap.parse_args()
    manifest = json.loads(args.manifest.read_text())
    prior = []
    for item in manifest['tables']:
        raw = (args.frontier / item['file']).read_bytes()
        fail_unless(hashlib.sha256(raw).hexdigest() == item['sha256'], item['file'])
        data = parse_table(raw)
        fail_unless(data is not None, item['file'])
        rows, states, halt = data
        if len(states) != 194:
            continue
        fail_unless(any(canonical(data, q) is not None for q in sorted(states)),
                    'No spanning root: ' + item['file'])
        prior.append(dict(file=item['file'], **graph_statistics(data)))
    raw = args.candidate.read_bytes()
    data = parse_table(raw)
    fail_unless(data is not None, 'Candidate is not a complete table')
    rows, states, halt = data
    fail_unless(len(states) == 194 and len(rows) == 388,
                'Candidate is not a 194-working-control binary table')
    fail_unless(canonical(data, 0) is not None,
                'Dense candidate must span from start zero')
    candidate = graph_statistics(data)
    distribution = dict(sorted(collections.Counter(x['working_indegree_one']
                                                   for x in prior).items()))
    fail_unless(len(prior) == 82, 'Pinned prior frontier must contain 82 graphs')
    fail_unless(distribution == {87: 2, 89: 1, 90: 5, 91: 11, 92: 23, 93: 37, 94: 3},
                'Unexpected pinned prior indegree-one distribution')
    fail_unless(candidate['working_indegree_one'] == 88,
                'Candidate does not have PA194G\'s distinguishing invariant')
    fail_unless(candidate['working_indegree_one'] not in distribution,
                'Indegree-one count does not separate candidate from corpus')
    result = dict(status='PASS', snapshot=manifest['snapshot'],
                  candidate=args.candidate.name,
                  candidate_sha256=hashlib.sha256(raw).hexdigest(),
                  candidate_statistics=candidate, prior_classes=len(prior),
                  prior_indegree_one_distribution=distribution,
                  reasoning='The count of working controls with indegree one is invariant under every stated cosmetic transformation.',
                  scope='Literal graph nonidentity only; not a consistency, runtime-correctness, or materiality proof.',
                  prior=prior)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'prior'}, indent=2))


if __name__ == '__main__':
    main()
