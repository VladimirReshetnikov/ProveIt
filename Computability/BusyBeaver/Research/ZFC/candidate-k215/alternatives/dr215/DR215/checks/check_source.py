#!/usr/bin/env python3
"""Two independent CFG resolutions and exact source delta, not bounded semantics."""
from pathlib import Path
import json
import source_language as sl
from common import cli, compact, pinned, require, sha, write_json


def run(root, work):
    """Bind the changed register effects to every primitive and guarded successor."""
    root, work = Path(root), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    raw = pinned(root, 'source/dr215.sites.json')
    rows = json.loads(raw)
    old = json.loads(pinned(root, 'inputs/st215.sites.json'))
    tree = sl.tree(rows)
    graph, count = sl.graph_arithmetic(rows)
    oldgraph, oldcount = sl.graph_arithmetic(old)
    require(graph == sl.graph_intervals(rows), 'New CFG resolvers disagree')
    require(oldgraph == sl.graph_intervals(old), 'Parent CFG resolvers disagree')
    require(count == oldcount == 6151, 'Guarded primitive census')
    require(sl.boundary(tree) == (0, 0, True), 'Source closure')
    metrics = sl.metrics(tree)
    require(metrics == {'dag_nodes': 201, 'leaf_occurrences': 4732,
                        'maximum_depth': 44, 'maximum_zero_run': 6}, 'Exact source census')
    changed = [i for i, (a, b) in enumerate(zip(rows, old)) if a != b]
    require(changed == [958, 963, 1136, 1141], 'Changed source ordinals')
    require(all(old[i][:2] == rows[i][:2] and old[i][2] == 3 and rows[i][2] == 5
                for i in changed), 'Only register C-to-B loads change')
    require([x[1] for x in graph] == [x[1] for x in oldgraph], 'Guarded successors changed')
    require([i for i, (a, b) in enumerate(zip(graph, oldgraph)) if a != b] == changed,
            'Unexpected register effect change')
    for i in changed:
        require(oldgraph[i][0][0] == graph[i][0][0] and
                oldgraph[i][0][1] == 3 and graph[i][0][1] == 5,
                'Effect not the declared parameter load')
    require(rows[4696] == ['00111', 'CC', 3] and
            graph[4696] == [['identity'], [0]], 'Ordinary return context')
    require(rows[4697] == ['010', 'CD', 1], 'Direct transfer entry')
    require(graph[4697:] == oldgraph[4697:], 'Direct transfer changed')
    require(rows[4717] == ['11101', 'CH', None], 'Single-guard halt')
    require(graph[:887] == oldgraph[:887] and graph[1170:] == oldgraph[1170:],
            'Changes escape the closed sixth-row interval')
    result = {
        'status': 'DUAL_CFG_AND_EXACT_LOCAL_DELTA_PASS', 'source_sha256': sha(raw),
        'metrics': metrics, 'source_boundary': list(sl.boundary(tree)),
        'arithmetic_and_interval_CFG_equal': True,
        'guarded_primitive_cases': count,
        'parent_and_new_all_guarded_successors_equal': True,
        'changed_source_ordinals': changed,
        'changed_data_effects': [{'ordinal': i, 'before': old[i], 'after': rows[i],
                                 'before_CFG': oldgraph[i], 'after_CFG': graph[i]}
                                for i in changed],
        'full_CFG_sha256': sha(compact(graph)),
        'rho6_interval': [887, 1170],
        'direct_transfer_unchanged_interval': [4697, 4732],
        'scope': 'Exact finite source binding; all-natural AX semantics follow the local macro proof.',
    }
    write_json(work / 'source.json', result)
    (work / 'full-CFG.json').write_bytes(compact(graph))
    return result


if __name__ == '__main__':
    cli(run)
