#!/usr/bin/env python3
"""Reconstruct the exact residual used in the negative experiment."""
import sys,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from whitehead_exposure.pd_fixture import presentation_from_pd
from whitehead_exposure.algebra import Budget,apply_whitehead,eliminate
from whitehead_exposure.selector import find_exposure
W,G,_=presentation_from_pd(json.loads((ROOT/'data/gordian_pd.json').read_text())['pd'])
trace=json.loads((ROOT/'data/gordian_rank-first.json').read_text())
assert trace['initial_words']==[list(w) for w in W] and trace['initial_alive']==list(G)
active=set(G);budget=Budget(100000000)
for move in trace['moves']:
    if move['kind']=='whitehead':
        W=apply_whitehead(W,move['multiplier'],set(move['subset']),budget,100000000)
    else:
        W=eliminate(W,move['relation'],move['generator'],budget,100000000)
        active.remove(move['generator'])
stats={};p=find_exposure(W,sorted(active),stats=stats)
assert p is None and stats['bridges']==0 and len(active)==11 and sum(map(len,W))==97684
output={'alive':sorted(active),'words':[list(w) for w in W],
        'provenance':'gordian_pd.json -> gordian_rank-first.json moves',
        'status':'INCONCLUSIVE','no_unit_bridges':True}
(ROOT/'data/gordian_residual_presentation.json').write_text(json.dumps(output,indent=2)+'\n')
print('Replayed residual: rank 11, 97684 letters, no unit bridges. No unknot conclusion.')
