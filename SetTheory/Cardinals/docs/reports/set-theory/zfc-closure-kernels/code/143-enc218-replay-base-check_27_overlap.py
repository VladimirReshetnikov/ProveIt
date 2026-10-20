#!/usr/bin/env python3
"""Independently validate the unbounded fixed-window overlap obstruction."""
import json
from pathlib import Path
import symbolic_contexts as O
D=Path(__file__).resolve().parent;ROOT=D.parent
records=json.loads((ROOT/'research218_encoding/RETURN_FULL_CONTRACTS.json').read_text())
record=next(x for x in records if x['site'][0]==0)
def readatoms(xs):
 return [('r',a[1],tuple(a[2])) if a[0]=='run' else ('l',a[1],a[3]) if a[0]=='list' else tuple(a) for a in xs]
def ownatoms(xs):return [('r',a[1],tuple(a[2])) if a[0]=='r' else tuple(a) for a in xs]
def headcanonical(q,d,L,R):
 # Convert representation to direction+1 without moving the physical head.
 if d==-1:
  a=L[0];assert a[0]=='r' and a[2][0]>0
  L=[O.atom(a[1],O.subone(a[2]))]+L[1:];R=[O.atom(a[1])]+R
 return q,O.norm(L),O.norm(R)
T=O.readtm(ROOT/'latest219_baseline/candidate-k219/k219.native.tm');T[113,0]=(0,-1,27)
new=O.Tape(113,readatoms(record['left']),readatoms(record['right']),record['direction']);new.advance(T,{});new.key()
newc=headcanonical(new.q,new.d,new.L,new.R)
oldrec=json.loads((D/'STATE27_TAG_AUDIT.json').read_text())['old_C8_frame_cases'][0]['27_entries'][2]
q,d,L,R=oldrec;oldc=headcanonical(q,d,ownatoms(L),ownatoms(R))
assert oldc[0]==newc[0]==27 and oldc[1]==newc[1]
common=0
for a,b in zip(oldc[2],newc[2]):
 if a!=b:break
 common+=1
assert common==4
assert oldc[2][:4]==[O.atom(0,2),O.atom(1,O.add(O.constant(61),O.variable(1))),O.atom(0),O.atom(1,O.add(O.constant(1),O.variable(4)))]
assert oldc[2][4]==O.atom(0,3)
assert newc[2][4:7]==[O.atom(0),O.atom(1),O.atom(0)]
result={'status':'UNBOUNDED_FIXED_WINDOW_OVERLAP_PROVED','old':'Third27/0 encounter during valid arbitrary-natural zeroCD8 interface at source000','new':'Same interface at113/0, modified incoming row0L27','same_state':27,'entire_left_half_equal':True,'common_right_prefix':'00 1^(61+gap) 0 1^(R2+1)','first_difference':'Old then000; new then010. This lies in the register file, beyond an arbitrarily long gap.','consequence':'For every finite radius, choose gap large enough that old/new entire centered windows agree. No fixed-neighbor or fixed-suffix discriminator can classify the combined domain. A farther scanning algorithm is not ruled out.','old_canonical':oldc,'new_canonical':newc}
(D/'STATE27_OVERLAP_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if not k.endswith('_canonical')},indent=2))
