#!/usr/bin/env python3
"""Replay the recorded 432-combination optimistic state-count screen.

This is not a semantic verifier. In particular, counterfactual zero-test exit
substitutions are screened without asserting that their invariants hold.
"""
from pathlib import Path
import argparse,copy,itertools,json,re,sys
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT))
import build as construction
c=construction.c
INC=('leaf','inc',1)

def word(t):return word(t[0])+word(t[1]) if c.isnode(t) else [t]
def substitute(t,values):
 it=iter(values)
 def go(t):return tuple(go(x) for x in t) if c.isnode(t) else next(it)
 result=go(t);assert next(it,None) is None
 return result

def run():
 primary=construction.normalize(c.read_grammar(ROOT/'inputs/primary.grammar.json'))
 gh=construction.normalize(c.read_grammar(HERE/'inputs/GH.grammar.json'))
 diagonal=construction.normalize(c.read_grammar(ROOT/'inputs/diagonal_D.grammar.json'))
 pw,gw=word(primary),word(gh)
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 c.MACROS[('leaf','dec',4)]=144
 results=[]
 for shape,t in [('P',primary),('G',gh),('D',diagonal)]:
  for binder,exchange,diag,breakd,zero,shift in itertools.product([0,1],[0,1],['A','D','H'],[0,1],[0,1],['sum','H','HS']):
   w=word(t);w[:18]=gw[:18] if binder else pw[:18]
   w[102:121]=gw[102:121] if exchange else pw[102:121]
   for i in (121,122,123):w[i]={'A':'node70','D':'node55','H':'node58'}[diag]
   w[-1]=('leaf','dec',4) if breakd else ('leaf','breakTo',1)
   tree=substitute(t,w)
   rows,nodes=construction.fixed_part({'sum':'GD','H':'GDH','HS':'GDHS'}[shift])
   if zero:rows[27,1]=(1,True,21);nodes['node22']=(('leaf','dec',8),('leaf','dec',6))
   c.machine=lambda:(rows,[]);c.raw_nodes=lambda:nodes
   raw,_,_=c.build(tree)
   opportunities=c.opportunities_fast(raw,{q:None for q,b in raw if q not in c.BOXSTATES})
   pairs=c.max_matching(opportunities)
   name=f'{shape}G{binder}Q{exchange}d{diag}b{breakd}z{zero}{shift}'
   results.append(dict(name=name,raw_states=len(raw)//2,matching_size=len(pairs),
                       optimistic_controls=len(raw)//2-len(pairs),
                       semantic_validation=False))
 assert len(results)==432
 return results

def check_recorded(results):
 old=[]
 for line in (HERE/'gd_variants.log').read_text().splitlines():
  m=re.match(r'^(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s',line)
  if m:old.append((m[1],int(m[2]),int(m[3]),int(m[4])))
 new=[(z['name'],z['optimistic_controls'],z['raw_states'],z['matching_size']) for z in results if z['optimistic_controls']<=194]
 assert new==old,'Recorded optimistic count log differs'
 return len(old)

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--check-recorded',action='store_true')
 a=p.parse_args();results=run()
 summary=dict(combinations=len(results),minimum_optimistic_controls=min(z['optimistic_controls']for z in results),
              below_194=sum(z['optimistic_controls']<194 for z in results),
              scope='Fixed grammar shapes and fixed core variants; optimistic local fold matching only.')
 if a.check_recorded:summary['recorded_qualifying_rows_matched']=check_recorded(results)
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps({'summary':summary,'results':results},indent=2)+'\n')
 print(json.dumps(summary))
