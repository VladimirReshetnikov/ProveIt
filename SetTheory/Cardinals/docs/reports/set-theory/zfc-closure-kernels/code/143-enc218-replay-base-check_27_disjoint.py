#!/usr/bin/env python3
"""Small exact word-unification obstruction; no numerical enumeration required."""
import json
from pathlib import Path
D=Path(__file__).resolve().parent
x=json.loads((D/'STATE27_OVERLAP_AUDIT.json').read_text());new=x['new_canonical'];old=x['old_canonical']
assert new[1]==old[1]
# After the two first forced separators, positive one-runs anchor the next zero-run.
# Equality requires oldgap=newgap and oldR2=newR2. At the next zero-run it requires3=1.
for side in [old,new]:
 assert side[2][0]==['r',0,[2]+[0]*12]
 assert side[2][1][0:2]==['r',1] and side[2][1][2][0]==61 and side[2][1][2][1]==1
 assert side[2][2]==['r',0,[1]+[0]*12]
 assert side[2][3][0:2]==['r',1] and side[2][3][2][0]==1 and side[2][3][2][4]==1
assert old[2][4]==['r',0,[3]+[0]*12]
assert new[2][4]==['r',0,[1]+[0]*12] and new[2][5]==['r',1,[1]+[0]*12]
# Check the positiveCD8 thirdvisit too: its separator is always length2.
tags=json.loads((D/'STATE27_TAG_AUDIT.json').read_text())
pos=tags['old_C8_frame_cases'][1]['27_entries'][2]
assert pos[3][0:4]==old[2][0:4]
assert pos[3][4]==['r',0,[2]+[0]*12]
result={'status':'FULL_FRAME_LANGUAGES_DISJOINT_FOR_THE_EXPLICIT_OVERLAP_PAIR','method':'Exact run-length word unification over independent natural parameters; no sample enumeration','necessary_equalities':['old_gap = new_gap from first positive one-run','old_R2 = new_R2 from second positive one-run','3 = 1 from following zero-run (old zeroCD8 guard), contradiction','2 = 1 from following zero-run (old positiveCD8 guard), contradiction'],'numerical_instantiations':0,'consequence':'No exact common configuration witness exists within these compared frame families, even allowing independent natural registers,gaps,and sparelists. Therefore this pair proves only unbounded fixed-window indistinguishability, not impossibility of every deterministic scanning handler.','other_old_visits':'First27/0 visit starts at least62zeros and second starts1zero, versus new2zeros, so those cannot coincide either.'}
(D/'STATE27_DISJOINT_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
