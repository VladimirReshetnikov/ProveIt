#!/usr/bin/env python3
"""Build PA194N6: radix-six formulas and no-push modus ponens.

All inputs are bundled and pinned. Python standard library only. This verifies
finite and symbolic simulation certificates, not an end-to-end kernel theorem.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
INPUT=HERE/'inputs'
EXPECTED_NATIVE='63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a'
EXPECTED_DENSE='36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4'
def sha(x):return hashlib.sha256(x).hexdigest()
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else[]
def build(out):
 assert __debug__ and not sys.flags.optimize,'Run with assertions enabled.'
 raw=s.read_table(INPUT/'parent6.raw.native.tm')
 folds=json.loads((INPUT/'parent6.folds.json').read_text())
 parent,aliases=s.apply_folds(raw,folds)
 oldreceipt=json.loads((INPUT/'parent6.receipt.json').read_text())
 assert sha(s.table_text(parent).encode())==oldreceipt['native_sha256']
 assert len(raw)==404 and len(folds)==8 and len(parent)==388
 assert raw[164,1]==(1,True,98)
 raw[164,1]=(1,True,114)
 child,aliases=s.apply_folds(raw,folds)
 assert {k:(parent[k],child[k])for k in child if parent[k]!=child[k]}=={
  (164,1):((1,True,98),(1,True,114))}
 cases=s.check_local_folds(raw,child,aliases,folds)
 assert len(cases['cases'])==32
 assert all(child[q,b]==parent[q,b]for q in c.BOXSTATES for b in(0,1))
 ns={k:tup(v)for k,v in json.loads((INPUT/'parent6.nodes.json').read_text()).items()}
 c.raw_nodes=lambda:ns
 grammar=c.read_grammar(INPUT/'pa194.grammar.json')
 oldsites,oldins,_=c.source(grammar)
 assert json.loads(json.dumps(oldins))==json.loads((INPUT/'parent6.instructions.json').read_text())
 assert len(oldins)==3795 and ns['node163']==('node6','node55')
 assert ns['node55']==('node49','node54')
 ns['node163']=('node6','node54')
 sites,ins,contracts=c.source(grammar)
 assert len(sites)==3776 and len(contracts)==4877
 lo,hi=3756,3775
 def rel(i):
  assert not lo<i<hi
  return i if i<=lo else i-(hi-lo)
 incoming=[];kept=0
 for pc,row in enumerate(oldins):
  if lo<=pc<hi:continue
  incoming += [[pc,t]for t in targets(row)if lo<=t<hi]
  n=2 if row[0]in('inc','dec')else 1
  assert tuple(row[:n])+tuple(rel(x)for x in row[n:])==ins[rel(pc)]
  kept+=1
 assert incoming==[[3750,3756]] and kept==3776
 expected=[('dec',4,4,1),('inc',1,2),('inc',6,3),('jump',0),
           ('dec',6,7,5),('inc',4,6),('jump',4)]
 for i,row in enumerate(ins[lo:lo+7]):
  n=2 if row[0]in('inc','dec')else 1
  assert tuple(row[:n])+tuple(x-lo for x in row[n:])==expected[i]
 valid=c.validate(child,contracts);assert valid['ok'],valid
 startup=s.startup(child,sites[25][0]);assert startup['steps']==58320
 dense,labels=s.dense_table(child,194)
 native_text=s.table_text(child);dense_text=s.table_text(dense)
 assert sha(native_text.encode())==EXPECTED_NATIVE
 assert sha(dense_text.encode())==EXPECTED_DENSE
 out.mkdir(parents=True,exist_ok=True)
 for name,text in [('machine.native.tm',native_text),('machine.tm',dense_text),
                   ('unfolded202.native.tm',s.table_text(raw))]:(out/name).write_text(text)
 for name,data in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),
                   ('instructions.json',ins),('nodes.json',ns),('folds.json',folds),
                   ('local_fold_cases.json',cases)]:dump(out/name,data)
 receipt={'family':'PA194N6','working_states':194,'rows':388,
  'fixed_controls':135,'AX_readers':67,'simultaneous_folds':8,'local_fold_cases':32,
  'formula_coefficient':6,'source_sites':len(sites),'source_contracts':len(contracts),
  'source_splice':{'parent_sites':3795,'removed_interval':[lo,hi],
   'incoming':incoming,'kept_sites':kept,'exact_relocation':True,'retained_copy_loop':expected},
  'native_edit':{'state':164,'read':1,'old':[1,'R',98],'new':[1,'R',114]},
  'runtime':valid,'startup':startup,'native_sha256':EXPECTED_NATIVE,'dense_sha256':EXPECTED_DENSE,
  'kernel_checked':False,'scope':'Complete finite/source/tape construction certificate. Logical calibration is an ordinary mathematical proof, not a new Lean/Rocq endpoint.'}
 dump(out/'receipt.json',receipt)
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=HERE.parent/'generated')
 build(p.parse_args().output)
