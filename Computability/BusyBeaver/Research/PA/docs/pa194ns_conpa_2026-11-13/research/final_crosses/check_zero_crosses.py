#!/usr/bin/env python3
"""Finite fixed-grammar crossing screen. No claim of global minimality.

Requires the delivered PA194NS package as --package. Tests five frozen
AX layouts with original final jump and final known-zero X decrement,
with/without the source-entry zero-X specialization.
It calculates exact maximum matching only in the documented three-step,
previous-bit reader-fold opportunity relation. A matching is a candidate,
not a complete source/PA certificate. No heuristic search is performed.
"""
from pathlib import Path
import argparse,hashlib,json,sys,itertools
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--package',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
sys.path.insert(0,str(args.package/'construction'));import build as base
c=base.c;c.machine=base.fixed;c.raw_nodes=base.nodes
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190;c.MACROS[('leaf','dec',6)]=21

def replace_close(t,new):
 if isinstance(t,tuple) and len(t)==3 and t[0]=='leaf' and t[1] in ('breakTo','dec'):return new
 return tuple(replace_close(x,new) for x in t) if c.isnode(t) else t

def normalize(t):
 if t=='node60':return inc,inc
 if t=='node61':return (inc,inc),(inc,inc)
 return tuple(normalize(x) for x in t) if c.isnode(t) else t

records=[]
for name in ('primary','R','Q','D','alternative68'):
 path=HERE/'inputs'/f'{name}.grammar.json';tree=normalize(c.read_grammar(path))
 for mode,entry_zero in itertools.product(('jump','zeroX'),(False,True)):
  def fixed():
   rows,labels=base.fixed()
   if entry_zero:rows[27,1]=(1,True,21)
   return rows,labels
  c.machine=fixed
  t=replace_close(tree,('leaf','breakTo',1) if mode=='jump' else ('leaf','dec',6))
  raw,idx,shape=c.build(t);incoming={}
  for (q,b),(w,d,n) in raw.items():incoming.setdefault(n,set()).add((w,d))
  ops=c.opportunities_fast(raw,{q for q,b in raw if q not in c.BOXSTATES})
  ops=[(a,b,actions) for a,b,actions in ops if incoming.get(a)=={(0,True)} and incoming.get(b)=={(1,True)}]
  matching=c.max_matching(ops);score=len(raw)//2-len(matching)
  record={'grammar':name,'closing':mode,'entry_zeroX':entry_zero,'grammar_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'raw_states':len(raw)//2,'AX_readers':len(shape),'opportunity_pairs':len(ops),'maximum_matching':len(matching),'optimistic_state_count':score,'pairs':matching}
  if score<194:
   bypair={(a,b):acts for a,b,acts in ops};candidates=[]
   choices=[[(a,b,[a0,a1]) for a0 in bypair[a,b][0] for a1 in bypair[a,b][1]] for a,b in matching]
   for folds in itertools.product(*choices):
    child,alias=base.fold(raw,folds)
    try:base.local_checks(raw,child,alias,folds)
    except AssertionError:continue
    candidates.append({'folds':folds,'table':base.text_table(child)})
   record['simultaneously_valid_matching_assignments']=candidates
  records.append(record);print(name,mode,entry_zero,len(raw)//2,len(matching),score,flush=True)
result={'status':'bounded screen complete','cases':len(records),'best_optimistic_state_count':min(r['optimistic_state_count'] for r in records),'sub194_found':any(r['optimistic_state_count']<194 for r in records),'scope':'Fixed five normalized grammar trees, two final closures, two source-entry interfaces, exact maximum matching within the inherited local three-step previous-bit fold template. Counts are not global lower bounds or source/logic proofs.','records':records}
args.output.write_text(json.dumps(result,indent=2)+'\n')
