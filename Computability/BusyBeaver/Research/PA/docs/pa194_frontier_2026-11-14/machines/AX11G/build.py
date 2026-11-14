#!/usr/bin/env python3
"""Construct AX11G from pinned PA194G; all writes go to an explicit output.
The copied compiler and runtimes are attributed in licenses/ and PROVENANCE.json.
These executable certificates are not a completed iPRA formalization.
"""
from pathlib import Path
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'construction'))
import compiler as c
import support as s
INC=('leaf','inc',1)
def tup(t):return tuple(map(tup,t))if isinstance(t,list)else t
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def normal(t):
 if t=='node60':return INC,INC
 if t=='node61':return (INC,INC),(INC,INC)
 return tuple(map(normal,t))if c.isnode(t)else t
def word(t):return word(t[0])+word(t[1])if c.isnode(t)else[t]
def grammar_json(t):
 idx={};rules={}
 def go(t):
  if not c.isnode(t):return t
  if t in idx:return idx[t]
  key='g'+str(len(idx));idx[t]=key;rules[key]=[go(x)for x in t];return key
 return {'root':go(t),'rules':rules}
def build(out,full=True):
 assert __debug__ and not sys.flags.optimize
 raw0=s.read_table(HERE/'inputs/raw.native.tm')
 nodes={k:tup(v)for k,v in json.loads((HERE/'inputs/nodes.json').read_text()).items()}
 assert nodes['node163']==('node6','node54')
 c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:nodes
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 oldg=normal(c.read_grammar(HERE/'inputs/grammar.json'))
 def change(t):return 'node49'if t==c.BREAK else tuple(map(change,t))if c.isnode(t)else t
 g=change(oldg)
 oldw,w=word(oldg),word(g)
 assert len(w)==len(oldw)==190 and oldw.count(c.BREAK)==1
 assert oldw[:-1]==w[:-1] and oldw[-1]==c.BREAK and w[-1]=='node49'
 oldsites,oldins,_=c.source(oldg);sites,ins,contracts=c.source(g)
 assert json.loads(json.dumps(oldins))==json.loads((HERE/'inputs/instructions.json').read_text())
 assert len(oldins)==3654 and len(ins)==3672
 # Resolve the unique edited leaf, then check the complete exterior graph.
 axpaths=[p for p,op,a in oldsites if op=='breakTo' and a==1]
 # Changed leaf located by first difference in site operation stream.
 oldops=[(op,a)for p,op,a in oldsites];newops=[(op,a)for p,op,a in sites]
 entry=next(i for i,(a,b)in enumerate(zip(oldops,newops))if a!=b)
 assert entry==3553 and oldins[entry][0]=='jump'
 def move(i):return i if i<=entry else i+18
 def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else()
 def reloc(row):
  n=2 if row[0]in('inc','dec')else 1
  return row[:n]+tuple(move(j)for j in row[n:])
 for i,row in enumerate(oldins):
  if i!=entry:assert reloc(row)==ins[move(i)],(i,row,ins[move(i)])
 for i,row in enumerate(ins):
  if not(entry<=i<entry+19):assert all(not(entry<j<entry+19)for j in targets(row))
 # Inserted push is identical, up to its sole normal exit, to an old push.
 def normblock(code,start):
  out=[]
  for row in code[start:start+19]:
   n=2 if row[0]in('inc','dec')else 1
   out.append(row[:n]+tuple(t-start for t in row[n:]))
  return out
 block=normblock(ins,entry)
 donor=next(i for i in range(len(oldins)-19)if normblock(oldins,i)==block)
 folds=json.loads((HERE/'inputs/folds.json').read_text())
 oldraw,_,_=c.build(oldg);raw,_,shape=c.build(g)
 assert len(raw)==402 and len(shape)==67 and len(folds)==7
 parent,pa=s.apply_folds(oldraw,folds);rows,aliases=s.apply_folds(raw,folds)
 parentdense,parentlabels=s.dense_table(parent,194)
 assert s.table_text(parentdense)==(HERE/'inputs/machine.tm').read_text()
 edits=[{'state':q,'read':b,'before':parent[q,b],'after':rows[q,b]}for q,b in sorted(rows)if parent[q,b]!=rows[q,b]]
 assert len(edits)==1 and edits[0]['before']==(0,False,302)and edits[0]['after']==(1,True,19)
 local=s.check_local_folds(raw,rows,aliases,folds)
 assert len(local['cases'])==28
 for q in c.BOXSTATES:
  for b in(0,1):assert rows[q,b]==parent[q,b]
 startup=s.startup(rows,sites[25][0]);assert startup['steps']==58154
 dense,labels=s.dense_table(rows,194)
 runtime=c.validate(rows,contracts)if full else None
 if full:assert runtime['ok'] and runtime['contracts']==4779
 out.mkdir(parents=True,exist_ok=True)
 for file,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
  (out/file).write_text(s.table_text(table))
 for file,obj in [('labels.json',labels),('nodes.json',nodes),('grammar.json',grammar_json(g)),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('local_folds.json',local)]:dump(out/file,obj)
 receipt={'family':'PA194AX11G','working_states':194,'transition_rows':388,'source_sites':len(ins),'source_outcomes':len(contracts),'fixed_controls':134,'reader_controls':67,'simultaneous_folds':7,'local_cases':28,'source_splice':{'old_entry':entry,'old_length':1,'new_length':19,'unchanged_exterior_sites':len(oldins)-1,'push_donor_entry':donor,'new_exit':entry+19,'all_exterior_successors_preserved':True,'no_exterior_entry_into_interior':True},'parent_dense_sha256':hashlib.sha256(s.table_text(parentdense).encode()).hexdigest(),'native_row_edits':edits,'startup':startup,'runtime':runtime,'dense_sha256':hashlib.sha256(s.table_text(dense).encode()).hexdigest(),'native_sha256':hashlib.sha256(s.table_text(rows).encode()).hexdigest(),'kernel_checked':False,'proof_scope':'Exact table, source splice and symbolic physical certificates. Unconditional iPRA calibration is not claimed.'}
 dump(out/'receipt.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE/'machine');ap.add_argument('--quick',action='store_true');a=ap.parse_args();build(a.output,not a.quick)
