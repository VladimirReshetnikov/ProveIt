from pathlib import Path
import sys,json
SRC=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'sources/context246/zfc-context246'
sys.path.insert(0,str(SRC/'code'))
import check_macro_inductions as m
from rebuild_machines import read_table
out={}
for name in ('gap103','posL73','posR73','gap103posL73','gap103posR73'):
 m.TABLE=read_table(Path(__file__).parent/(name+'.tm'))[0]
 m.WORD_IDENTITY_PROVED=False;m.BLOCK_PROOFS.clear();m.DERIVED.clear()
 m.prove_blocks();m.prove_word_identity()
 p,s=m.E.var('width_pre'),m.E.var('width_suf')
 x,y=m.E.var('x'),m.E.var('y')
 a,b=m.Blocks('B','pre'),m.Blocks('B','suf')
 l,z=m.Context('arbitrary_left'),m.Blank()
 altered_tail='gap103' in name
 altered_pos='pos' in name
 results=[]
 # For positive decrement x+1 denotes every positive value.
 extension=[]
 if altered_pos:extension=m.B(m.E(1))*(1 if altered_tail else 2)
 cost=2*(p+x+s+3)+10+(4 if altered_tail else 0)+(2 if 'L73' in name else 0) if altered_pos else 2*p+4
 results.append(m.prove('positive_decrement',m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x+1),b,z]),
  m.Conf(48,'L',[m.bit(1),l],[a]+m.B(x)+[b]+extension+[z]),cost,m.E(),True))
 suffix=m.B(y)+[b,z]
 results.append(m.prove('zero_decrement',m.Conf(95,'R',[l],[a,m.bit(0),m.bit(0)]+suffix),
  m.Conf(112,'L',[l],[a]+m.B(m.E())+suffix),2*p+7,m.E(-1),True))
 extension=[] if altered_tail else m.B(m.E(1))
 results.append(m.prove('increment',m.Conf(73,'R',[l],[a,m.bit(0),m.bit(0),m.ones(x),b,z]),
  m.Conf(48,'L',[l],[a]+m.B(x+1)+[b]+extension+[z]),2*(p+x+s+2)+(11 if altered_tail else 7),m.E(-1),True))
 results.extend(m.prove_marks())
 out[name]=results
 print(name,[(r['name'],r['steps']) for r in results[:3]],flush=True)
(Path(__file__).parent/'neutral_macro_proofs.json').write_text(json.dumps(out,indent=2)+'\n')
