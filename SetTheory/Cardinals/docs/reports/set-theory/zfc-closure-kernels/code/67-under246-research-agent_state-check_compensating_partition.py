#!/usr/bin/env python3
"""Independent finite coverage check for the lazy incoming-action partitions.

This checks coverage and disjointness, not the affine rejection premises.
It uses only the Python standard library and recursively partitions cubes.
"""
import json,math,ast,gzip,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent

def check_cover(records,domains):
    """Prove exact coverage by case splitting, returning represented count."""
    assert records,'uncovered branch'
    if any(not record for record in records):
        assert len(records)==1,'a universal cell overlaps another rejected cell'
        return math.prod(map(len,domains.values())),1
    common=set(records[0])
    for record in records[1:]:common.intersection_update(record)
    # The lazy search must have fixed some first queried edge in every
    # descendant. No trust is placed in the original choice/order of that edge.
    assert common,'no shared partition variable'
    key=sorted(common)[0]
    assert key in domains
    children={action:[] for action in domains[key]}
    for record in records:
        assert record[key] in children
        children[record[key]].append({k:v for k,v in record.items() if k!=key})
    remaining={k:v for k,v in domains.items() if k!=key}
    results=[check_cover(child,remaining) for child in children.values()]
    # Different children prescribe distinct actions for the same edge, hence
    # cannot overlap. The recursive check covers every possible edge action.
    return sum(r[0] for r in results),1+sum(r[1] for r in results)

def main():
    families=json.loads((HERE/'incoming_extended_action_candidates.json').read_text())
    path=HERE/'incoming_extended_compensating_search.json'
    raw=path.read_bytes();data=json.loads(raw)
    report={}
    for q,v in data.items():
        opts={str((str(a),b)):[(w,'R' if d==1 else 'L',str(r)) for w,d,r in actions]
              for edge,actions in families[q]['incoming'].items()
              for a,b in [ast.literal_eval(edge)]}
        keys=list(opts);dims=tuple(len(opts[k]) for k in keys)
        records=[]
        assert not v['solutions'] and not v['unfinished_frontier']
        for leaf in v['rejected_partial_assignments']:
            assignment={k:tuple(row) for k,row in leaf['assignment'].items()}
            assert set(assignment)<=set(keys)
            records.append(assignment)
        count,nodes=check_cover(records,opts)
        assert count==math.prod(dims)==v['raw_combinations']
        report[q]=dict(status='PASS',dimensions=list(dims),complete_assignments=count,
            rejected_partial_assignments=len(v['rejected_partial_assignments']),
            independently_constructed_partition_nodes=nodes,
            pairwise_disjoint=True,all_complete_assignments_covered=True)
    with gzip.GzipFile(filename=str(path)+'.gz',mode='wb',mtime=0) as out:out.write(raw)
    result=dict(status='PASS',family_checks=report,
       covered_complete_assignments=sum(v['complete_assignments'] for v in report.values()),
       original_certificate_sha256=hashlib.sha256(raw).hexdigest(),
       scope='Finite Cartesian coverage and disjointness only. This does not establish a global lower bound or validate each affine rejection premise.')
    (HERE/'incoming_partition_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
