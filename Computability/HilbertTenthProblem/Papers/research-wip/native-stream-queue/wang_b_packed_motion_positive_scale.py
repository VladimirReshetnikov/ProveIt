"""Positive scale coordinate for complete chronological Wang head motion.

The old motion semantics and its limitations are unchanged. Only the
native X-bound coordinate is reparametrized; no program control is added.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random

import native_binary_positive_scale as scale
import wang_b_packed_motion as parent


def build():
    p=scale.rewrite(parent.build(),prefix='native__')
    old=p['positive_scale_parent']
    assert p['parameters']==old['parameters'] and p['interfaces']==old['interfaces']
    assert p['comparisons'][:3]==old['comparisons'][:3]
    assert [row for row in p['source'] if not row[0].startswith('native__')]==[
        row for row in old['source'] if not row[0].startswith('native__')]
    return dict(p,packed_motion_positive_scale=True)


polynomial_source=scale.polynomial_source
ledger=scale.ledger
degree_bound=scale.degree_bound
lift_to_parent=scale.lift_to_parent
project_from_parent=scale.project_from_parent


def outer_path(initial,head,actions):
    """Outer fixture only: native entries are positive placeholders."""
    values,trace=parent.positive_path(initial,head,actions)
    del values['native__w']
    return values,trace


def verify():
    p=build();audit=scale.identity_audit(p,384,2411834)
    rng=random.Random(188241);paths=steps=lefts=0
    outer=[row for row in p['source'] if not row[0].startswith('native__')]
    at=lambda e,v:e[v] if isinstance(v,str) else v
    for n in range(1,13):
      for trial in range(16):
        initial=rng.randrange(128);head=1<<rng.randrange(6);h=head;actions=[]
        for j in range(n):
            a=rng.choice(['mark','stay','right']+(['left'] if h>1 else []))
            actions.append(a);h=h//2 if a=='left' else h*2 if a=='right' else h
        values,trace=outer_path(initial,head,actions)
        e=scale.execute(outer,values)
        assert all(at(e,a)==at(e,b) for a,b in p['comparisons'][:3])
        H,M,Z=[e[p['interfaces'][k]] for k in ('joined_H','joined_M','joined_Z')]
        S=e[p['interfaces']['native_scale']]
        assert H&M==Z and 0<=min(H,M,Z)<=max(H,M,Z)<S and S&(S-1)==0
        # This lift is positive on all positive supplied coordinates,
        # independently of whether the placeholder native equations hold.
        restored=lift_to_parent(p,values)
        assert min(restored.values())>0 and project_from_parent(p,restored)==values
        paths+=1;steps+=n;lefts+=actions.count('left')
    l=ledger(p)
    assert l['certificate']==dict(operations=188,multiplications=81,additions_subtractions=107,equations=18,witnesses=34)
    assert l['polynomial']['operations']==241 and l['polynomial']['degree_upper_bound']==316
    source,out=polynomial_source(p)
    return dict(status='PASS_WANG_B_PACKED_MOTION_POSITIVE_SCALE',ledger=l,audit=audit,
        genuine_outer_paths=paths,physical_steps=steps,left_moves=lefts,
        source_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest(),
        inherited_invalid_shape_checks=parent.rejected_local_shapes(),
        example=dict(source=source,comparisons=p['comparisons'],parameters=p['parameters'],
                     auxiliaries=p['auxiliaries'],interfaces=p['interfaces'],output=out),
        scope='Full positive-zero bijection with packed Wang motion under native scale-coordinate change. '
              'Read/mark and left/right/stay semantics and endpoint projection unchanged. '
              'No finite instruction control, ordinary-TM input coding or universal bound; '
              'outer paths use placeholders, not full positive Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledger'])
