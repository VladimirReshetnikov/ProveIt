#!/usr/bin/env python3
"""Prove a nine-state local variant with an explicit, unacceptable zero effect."""
import sys,json
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]/'context_folds/recovered/64/baseline/context246';sys.path.insert(0,str(BASE/'code'))
import check_macro_inductions as p
from prove_borrowed_tail import derive
p.TABLE[75,0]=(1,'R',131);del p.TABLE[255,0];del p.TABLE[255,1]
p.prove_blocks();word=p.prove_word_identity()
x,y=p.E.var('x'),p.E.var('y');A,S=p.Blocks('B','pre'),p.Blocks('B','suf');L,Z=p.Context('opaque_left'),p.Blank()
proofs=[]
proofs.append(derive('increment_append_zero',p.Conf(73,'R',[L],[A,p.bit(0),p.bit(0),p.ones(x),S,Z]),p.Conf(48,'L',[L],[A]+p.B(x+1)+[S]+p.B(p.E())+[Z])))
proofs.append(derive('positive_decrement',p.Conf(95,'R',[L],[A,p.bit(0),p.bit(0),p.ones(x+1),S,Z]),p.Conf(48,'L',[p.bit(1),L],[A]+p.B(x)+[S,Z])))
proofs.append(derive('zero_transfers_from_following_positive',p.Conf(95,'R',[L],[A,p.bit(0),p.bit(0)]+p.B(y+1)+[S,Z]),p.Conf(112,'L',[L],[A]+p.B(p.E(1))+p.B(y)+[S,Z])))
proofs.append(derive('zero_empties_following_zero',p.Conf(95,'R',[L],[A,p.bit(0),p.bit(0)]+p.B(p.E())+[S,Z]),p.Conf(112,'L',[L],[A]+p.B(p.E(1))+[p.bit(0),S,Z])))
out=dict(status='PARTIAL_RESULT_WITH_WRONG_ZERO_EFFECT',working_states=245,edits={'75/0':[1,'R',131]},removed=[255],macros=proofs,scope='Universal local contracts. The zero effect changes primary data and can remove a following zero-valued block; it is not the required register-machine simulation. No valid blank bootstrap or consistency equivalence follows.')
Path(__file__).with_name('transfer_zero_inductions.json').write_text(json.dumps(out,indent=2)+'\n')
for x in proofs:print(x['name'],x['steps'],x['motion'])
