#!/usr/bin/env python3
"""Compare the exact primary and A/D companion 194-state control graphs."""
from pathlib import Path
import argparse
import collections
import json
import check as independent


def compare():
    jobs = {j['family']: j for j in json.loads((independent.HERE/'jobs.json').read_text())}
    tables = {}
    graph_hashes = {}
    for name in ('PA194', 'PA194_AD'):
        job = jobs[name]
        path = independent.PACKAGE/job['native']
        assert independent.sha(path.read_bytes()) == job['native_sha256']
        table, states, halt = independent.parse(path, 194)
        tables[name] = (table, states, halt)
        graph_hashes[name] = independent.unrooted(table, states, halt)[0]
    primary, states, halt = tables['PA194']
    companion, other_states, other_halt = tables['PA194_AD']
    assert states == other_states and halt == other_halt == 254
    assert graph_hashes['PA194'] != graph_hashes['PA194_AD']
    primary_counts = collections.Counter((w, d) for w, d, t in primary.values())
    companion_counts = collections.Counter((w, d) for w, d, t in companion.values())
    reflected_counts = collections.Counter((w, 'L' if d == 'R' else 'R')
                                          for w, d, t in primary.values())
    assert companion_counts != reflected_counts
    changes = [{'state': q, 'read': r, 'primary': primary[q, r], 'AD': companion[q, r]}
               for q, r in sorted(primary) if primary[q, r] != companion[q, r]]
    assert len(changes) == 3
    return {
        'status': 'PASS', 'primary_family': 'PA194', 'companion_family': 'PA194_AD',
        'same_working_controls': True, 'distinct_root_free_control_graphs': True,
        'root_free_graph_hashes': graph_hashes,
        'not_related_by_global_tape_reflection': True,
        'reflection_obstruction': 'global counts of (written bit, direction) differ',
        'primary_action_counts': {str(k): v for k, v in sorted(primary_counts.items())},
        'reflected_primary_action_counts': {str(k): v for k, v in sorted(reflected_counts.items())},
        'AD_action_counts': {str(k): v for k, v in sorted(companion_counts.items())},
        'different_native_rows': changes,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(compare(), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    print(result, end='')
