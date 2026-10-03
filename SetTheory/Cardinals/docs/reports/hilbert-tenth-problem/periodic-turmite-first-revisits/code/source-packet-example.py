"""A first phase/stencil event at time 2*10**100, computed without replay."""
import json
from dataclasses import asdict
from observations import Clause,solve

M=10**100
rule='RL'; tile=[[0,1],[1,0]]
clause=Clause(headings=(0,),congruences=((1,0,0,M),),
              stencil=((0,0,0),(-1,-1,1)))
result,hit=solve(rule,tile,clauses=(clause,))
if result.repeat is not None or hit is None or hit.time!=2*M:
    raise RuntimeError('Huge first-hit example failed')
print(json.dumps({'rule':rule,'tile':tile,'defects':[],
                  'clause':asdict(clause),'first_hit':asdict(hit),
                  'compressed_lanes':len(result.lanes)},indent=2))
