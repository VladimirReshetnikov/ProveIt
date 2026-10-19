#!/usr/bin/env python3
"""Universal local identities for a borrowed decoder-tail closure.
Not a complete consistency machine: the counter return remains unproved.
"""
import sys,json,argparse,hashlib
from pathlib import Path
BASE=Path(__file__).resolve().parents[1]/'context_folds/recovered/64/baseline/context246'
sys.path.insert(0,str(BASE/'code'))
import check_macro_inductions as p

def derive(name,begin,end):
 c=begin.copy();cost=p.E();motion=p.E();trace=[]
 for _ in range(1000):
  c.left=p.norm(c.left,c.state==48 and c.side=='L');c.right=p.norm(c.right)
  if c.key()==end.key():return dict(name=name,status='PASS',universal=True,steps=str(cost),motion=str(motion),trace=trace)
  v=p.apply_list_induction(c,cost,motion,trace)
  if v is None:cost,motion=p.literal_or_power(c,cost,motion,trace)
  else:cost,motion=v
 raise AssertionError('proof did not finish')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--borrowed',type=int,choices=[33,126],default=33);args=ap.parse_args();borrowed=args.borrowed
 table=p.TABLE.copy();del table[255,0];del table[255,1]
 table[75,0]=(0,'R',63);table[48,0]=(1,'L',131);table[131,0]=(1,'L',borrowed);p.TABLE=table
 p.prove_blocks();word=p.prove_word_identity();x,y=p.E.var('x'),p.E.var('y');A=p.Blocks('B','pre');S=p.Blocks('B','middle');L=p.Context('opaque_left');Z=p.Blank()
 proofs=[]
 proofs.append(derive('positive_decrement',p.Conf(95,'R',[L],[A,p.bit(0),p.bit(0),p.ones(x+1),S]+p.B(p.E(1))+[Z]),p.Conf(48,'L',[p.bit(1),L],[A]+p.B(x)+[S]+p.B(p.E(1))+[Z])))
 p.WORD_IDENTITY_PROVED=False
 proofs.append(derive('zero_decrement',p.Conf(95,'R',[L],[A,p.bit(0),p.bit(0)]+p.B(y)+[S,Z]),p.Conf(112,'L',[L],[A]+p.B(p.E())+p.B(y)+[S,Z])))
 p.WORD_IDENTITY_PROVED=True
 proofs.append(derive('increment_spare_phase',p.Conf(73,'R',[L],[A,p.bit(0),p.bit(0),p.ones(x),S]+p.B(p.E(1))+[Z]),p.Conf(48,'L',[L],[A]+p.B(x+1)+[S]+p.B(p.E())+p.B(p.E(1))+[Z])))
 out=dict(status='PARTIAL_RESULT',working_states=len(table)//2,scope='Universal arithmetic only. No correct program-counter return or blank bootstrap established.',edits={'75/0':[0,'R',63],'48/0':[1,'L',131],'131/0':[1,'L',borrowed]},removed=[255],borrowed_state=borrowed,source_sha256=hashlib.sha256((BASE/'machine/zfc_prefix246_old.tm').read_bytes()).hexdigest(),spare_invariant='Final spare equals1. Increment turns it into0 and appends1, preserving the invariant.',word_identity=word,blocks=list(p.BLOCK_PROOFS.values()),macros=proofs)
 here=Path(__file__).resolve().parent;(here/f'borrowed_tail_{borrowed}_inductions.json').write_text(json.dumps(out,indent=2)+'\n');(here/f'borrowed_tail_{borrowed}_partial.tm').write_text('#! start 95\n# INCOMPLETE: program-counter return and bootstrap are unproved.\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(table.items())))
 print(json.dumps({k:v for k,v in out.items()if k not in['blocks','macros','word_identity']},indent=2))
 for x in proofs:print(x['name'],x['steps'],x['motion'])
if __name__=='__main__':main()
