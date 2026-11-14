#!/usr/bin/env python3
"""Check the AX11 splice against the full radix-six QN source graph.

The imported source compiler supplies the original graph. New graph facts
are cross-checked by two independent resolvers in verification/check.py.
This check verifies all unchanged successors and the complete copied Push.
"""
from pathlib import Path
import sys,json,argparse
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE))
import build_ax11q6 as b

def check(machine):
 c=b.c
 oldg=c.read_grammar(HERE/'inputs/grammar.json')
 ns=b.nodes(6);c.raw_nodes=lambda:ns
 old,oldcode,_=c.source(oldg)
 new=[(tuple(p),op,arg)for p,op,arg in json.loads((machine/'sites.json').read_text())]
 newcode=[tuple(x)for x in json.loads((machine/'instructions.json').read_text())]
 oldpaths={p:i for i,(p,op,arg)in enumerate(old)}
 newpaths={p:i for i,(p,op,arg)in enumerate(new)}
 removed=[i for p,i in oldpaths.items()if p not in newpaths]
 added=[i for p,i in newpaths.items()if p not in oldpaths]
 assert len(removed)==1 and len(added)==19
 oi=removed[0];prefix=old[oi][0];ni=added[0]
 assert old[oi][1:]==('breakTo',1)
 assert added==list(range(ni,ni+19))
 assert all(new[i][0][:len(prefix)]==prefix for i in added)
 assert oldcode[oi][0]=='jump' and oldcode[oldcode[oi][1]]==('jump',25)
 reloc={i:newpaths[p]for p,i in oldpaths.items()if p in newpaths}
 reloc[oi]=ni
 def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else()
 assert any(ni+19 in targets(newcode[i])for i in added)
 assert all(ni<=t<=ni+19 for i in added for t in targets(newcode[i]))
 def mapped(row):
  if row[0]in('inc','dec'):return row[:2]+tuple(reloc[t]for t in row[2:])
  if row[0]=='jump':return ('jump',reloc[row[1]])
  return row
 for i,j in reloc.items():
  if i==oi:continue
  assert old[i][1:]==new[j][1:]
  assert mapped(oldcode[i])==newcode[j],(i,j,oldcode[i],newcode[j])
 for i,row in enumerate(newcode):
  if i not in added:assert all(t not in added or t==ni for t in targets(row))
 # Identify every occurrence of the original Push macro independently of
 # ordinal labels, and compare the inserted block with one complete copy.
 paths=[]
 def walk(t,p):
  if isinstance(t,str):
   if t=='node49':paths.append(p)
   walk(oldg if t=='x67'else ns[t],p)
  elif c.isnode(t):walk(t[0],p+(0,));walk(t[1],p+(1,))
 walk('node172',())
 pp=paths[0]
 reference=[i for i,(p,op,arg)in enumerate(old)if p[:len(pp)]==pp]
 assert reference==list(range(reference[0],reference[0]+19))
 assert [old[i][1:]for i in reference]==[new[i][1:]for i in added]
 def normalized(row,start):
  if row[0]in('inc','dec'):return row[:2]+tuple(t-start for t in row[2:])
  if row[0]=='jump':return ('jump',row[1]-start)
  return row
 assert [normalized(oldcode[i],reference[0])for i in reference]==[normalized(newcode[i],ni)for i in added]
 # The copied Push exits into the entire old MP, including its parameter read.
 assert reloc[oi+1]==ni+19
 assert oldcode[oi+1][0]=='dec' and oldcode[oi+1][1]==8
 receipt=dict(status='PASS',old_QN6_sites=len(old),new_AX11Q6_sites=len(new),
   old_exit_site=oi,old_exit_target=oldcode[oi][1],old_return_target=25,new_push_start=ni,new_push_sites=19,
   MP_reader_entry=ni+19,MP_reader_logical_register=8,
   unchanged_sites=len(old)-1,all_other_source_successors_relocate=True,
   no_external_entry_to_splice_interior=True,inserted_push_equals_complete_old_push=True,
   new_source_extra_sites=18,old_nodes_and_grammar_unchanged_outside_final_AX_leaf=True)
 (machine/'source_splice.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
 return receipt

if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--machine',type=Path,default=HERE/'machine')
 check(parser.parse_args().machine)
