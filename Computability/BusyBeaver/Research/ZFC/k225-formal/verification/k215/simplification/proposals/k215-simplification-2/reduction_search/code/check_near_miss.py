#!/usr/bin/env python3
"""Finite hypotheses of the written second-selector incidence lemma."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1];path=root/'inputs/cm215.native.tm';T={}
for line in path.read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,c,w,d,z=line.split();T[int(q),int(c)]=(int(w),d,int(z))
assert hashlib.sha256(path.read_bytes()).hexdigest()=='e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252'
incoming=lambda q:{k:v for k,v in T.items()if v[2]==q}
assert incoming(176)=={(52,0):(0,'L',176)}
assert incoming(52)=={(156,1):(1,'R',52),(165,0):(0,'R',52),(190,1):(1,'R',52),(193,0):(0,'R',52),(193,1):(1,'R',52)}
assert incoming(165)=={(151,1):(1,'R',165)}
assert incoming(193)=={(131,1):(1,'R',193),(145,1):(1,'R',193)}
assert incoming(211)=={(220,0):(0,'R',211)}
assert T[176,1]==T[211,1]==(1,'R',129)
assert T[176,0]==(0,'R',185) and T[211,0]==(0,'R',159)
u=[q for(q,c),v in T.items()if c==0 and v==(0,'R',159)]
v=[q for(q,c),v in T.items()if c==0 and v==(0,'R',185)]
assert u==[211] and v==[176]
print(json.dumps({'status':'SECOND_SELECTOR_INCIDENCE_HYPOTHESES_PASS','statement':'Starting at0 on any tape: current0 at176 implies left1; at211 left0. Thus roles distinguishable by predecessor cell, but no214 realization supplied.','three_step_template_obstruction':{'providers_0R159':u,'providers_0R185':v,'reason':'211 must be rewritten and176 deleted, so neither required unchanged provider remains.'}},indent=2))
