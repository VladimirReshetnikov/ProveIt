#!/usr/bin/env python3
"""Replay every blank start of the 52 physical 193-control trial graphs.

Every divergence certificate is an exact outward zero-reading self-loop;
no timeout is treated as nonhalting. The distinct coefficient-three logical
rejection is attributed separately and is not checked by this script.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[1]/'comparison'))
from graph_tools import parse,canonical,sha


def run(table,states,start,bound=1000):
    q,head,ones=start,0,set()
    for steps in range(bound+1):
        if q not in states:
            return {'outcome':'halt','steps':steps,'state':q,
                    'head':head,'ones':sorted(ones)}
        read=int(head in ones)
        write,right,target=table[q,read]
        blank=not any((x>=head if right else x<=head)for x in ones)
        if read==0 and target==q and blank:
            return {'outcome':'outward_ray','steps':steps,'state':q,
                    'head':head,'ones':sorted(ones),
                    'ray_row':[q,0,write,'R'if right else'L',q]}
        if steps==bound:
            return {'outcome':'unresolved','steps':steps}
        (ones.add if write else ones.discard)(head)
        head+=1 if right else -1
        q=target
    raise AssertionError


def main():
    assert __debug__,'Run without Python -O.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    manifest=json.loads((HERE/'manifest.json').read_text())
    frozen=json.loads(gzip.decompress((HERE/'certificates.json.gz').read_bytes()))
    assert len(manifest)==len(frozen)==52
    by_id={r['class_id']:r for r in frozen}
    seen,counts=set(),Counter()
    maximum=0
    for item in manifest:
        path=HERE/item['table_file']
        assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256']
        table,states=parse(path)
        assert len(states)==193 and len(table)==386
        canonical_tuple=canonical(table,states)
        assert canonical_tuple is not None and canonical_tuple not in seen
        seen.add(canonical_tuple)
        assert sha(canonical_tuple)==item['class_id']
        fresh=[{'start':q,**run(table,states,q)}for q in sorted(states)]
        assert fresh==by_id[item['class_id']]['runs']
        local=Counter(r['outcome']for r in fresh)
        assert dict(local)==item['counts']
        counts.update(local)
        maximum=max(maximum,max(r['steps']for r in fresh))
    assert counts=={'halt':106,'outward_ray':9930} and maximum==117
    result={'status':'PASS','physical_graph_classes':52,
            'blank_starts_replayed':sum(counts.values()),'outcomes':dict(counts),
            'maximum_steps_to_certificate':maximum,'unresolved':0,
            'certificate_equality':'Full per-start trace endpoints and exact half-line conditions, not digest-only.',
            'logical_coefficient_three_rejection':'Not rerun; separate attributed proof in the pinned repository.',
            'not_a_global_state_lower_bound':True}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
