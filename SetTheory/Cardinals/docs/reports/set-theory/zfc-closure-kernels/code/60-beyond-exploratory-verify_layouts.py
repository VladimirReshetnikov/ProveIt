#!/usr/bin/env python3
"""Portable short-zero geometry/history replay; no beam search or TM claim.

Verifies all 238 first-step rotations and the saved four histories. The
30,564-layout beam count and 12 contextual-emission failures remain explicitly
historical records; this script checks their recorded data but does not rerun
the beam or the contextual emitter.
"""
import argparse,hashlib,json,sys,time
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import rotate_search as rotations

def tuple_tree(x):return tuple(map(tuple_tree,x)) if isinstance(x,list) else x
def normalize(data):return {int(q):tuple_tree(pair) for q,pair in data['nodes'].items()},data['root']
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def metrics(nodes,root):
    prefix,maximum,depth=rotations.zero_metrics(nodes,root)
    excess=sum(max(0,rotations.zero_metrics(nodes,q)[0]-6) for q in nodes)
    return [len(nodes),excess,maximum,depth]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions required; do not use -O or -OO.')
    began=time.monotonic()
    manifest=json.loads((HERE/'import_manifest.json').read_text())
    for path,record in manifest.items():assert sha(HERE/path)==record['sha256'],('changed input',path)
    assert sha(HERE/'data/original203.json')=='9bcbe8c5927b28268f227ed1e40def5a13093928c8edb2b2c6cd89e6ae8df33b'
    source,root=normalize(json.loads((HERE/'data/original203.json').read_text()))
    assert metrics(source,root)==[203,16,7,34]
    choices=rotations.options(source);assert len(choices)==238
    distribution=Counter();identities=set()
    for node,expression,kind in choices:
        changed,newroot=rotations.mutate(source,root,node,expression)
        measured=metrics(changed,newroot)
        assert measured[2]>=7
        distribution[(measured[0],measured[2],measured[3])]+=1
        identities.add(repr(tuple(changed.values())))
    assert len(identities)==238
    recorded=json.loads((HERE/'records/short-zero-layout.json').read_text())
    assert recorded['baseline']==metrics(source,root)
    assert len(recorded['rounds'])==12
    assert recorded['rounds'][0]['states_examined']==239
    assert recorded['rounds'][-1]['states_examined']==30564
    assert recorded['parameters']['width']==12 and recorded['parameters']['depth']==12
    histories=[]
    for index,record in enumerate(recorded['short_zero_layouts']):
        nodes,r=source,root
        for raw in record['history']:
            node,expression,kind=tuple_tree(raw)
            assert (node,expression,kind) in rotations.options(nodes)
            nodes,r=rotations.mutate(nodes,r,node,expression)
        expected,eroot=normalize(record)
        assert (nodes,r)==(expected,eroot)
        assert metrics(nodes,r)==record['metrics'] and record['metrics'][2]==6
        histories.append(dict(index=index,rewrites=len(record['history']),metrics=record['metrics'],closed_reassociation_history_replayed=True))
    assert len(histories)==4 and [x['metrics'][0] for x in histories]==[204,204,204,205]
    combined=json.loads((HERE/'records/combined-source-metrics.json').read_text())['results']
    failures=json.loads((HERE/'records/combined-runtime-prices.json').read_text())
    assert len(combined)==len(failures)==12
    expected_kinds={'direct_transfer':5650,'output_prefill2':5590,'zerohead_add8':5770}
    combined_reports=[]
    for record in combined:
        name=Path(record['path']).name
        nodes,r=normalize(json.loads((HERE/'data'/name).read_text()))
        m=metrics(nodes,r)
        leaves=sum(1 for p,e in rotations.leaves(rotations.unfold(nodes,r)))
        assert len(nodes)==record['nodes'] and leaves==record['leaves']==expected_kinds[record['kind']]
        assert m[2]==record['maxzero'] and list(rotations.bounds(rotations.unfold(nodes,r)))==record['bounds']
        matching=[f for f in failures if Path(f['input']).name==name]
        assert len(matching)==1
        f=matching[0]
        assert f['status']=='affine_failure' and f['case']==139 and f['scan8'] is True and f['decoder_nodes']==len(nodes)
        assert f['operation']=='CC' and f['physical']==2 and f['zero'] is None
        combined_reports.append(dict(layout=record['layout'],variant=record['kind'],nodes=len(nodes),leaves=leaves,max_zero=m[2],recorded_first_affine_failure=f['case']))
    original_prices=json.loads((HERE/'records/short-zero-price.json').read_text())
    assert original_prices['input_sha256']==sha(HERE/'records/short-zero-layout.json')
    assert len(original_prices['answers'])==4 and all(x['status']=='affine_failure' and x['case']==139 for x in original_prices['answers'])
    answer=dict(status='PASS',scope=__doc__,original_metrics=metrics(source,root),
        first_step_recipes=238,first_step_kinds=dict(Counter(x[2] for x in choices)),
        first_step_distribution=[dict(nodes=n,max_zero=z,depth=d,count=count) for (n,z,d),count in sorted(distribution.items())],
        no_first_step_maximum_below_seven=True,saved_histories=histories,
        historical_beam_unique_layout_count=30564,beam_search_reexecuted=False,
        combined_input_geometry=combined_reports,contextual_failures_reexecuted=False,
        mathematical_scope='Closed-subroutine reassociations preserve source semantics. Geometry and historical sufficient-checker failures give no TM state reduction or minimum.',
        elapsed_seconds=time.monotonic()-began)
    if args.output:args.output.write_text(json.dumps(answer,indent=2)+'\n')
    print(json.dumps(answer,indent=2))

if __name__=='__main__':main()
