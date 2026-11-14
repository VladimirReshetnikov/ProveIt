#!/usr/bin/env python3
"""Construct PA194H6: radix six and no-push MP, with cached-only Shift."""
from pathlib import Path
import argparse,hashlib,json,sys,ast,re
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
INPUT=HERE/'inputs'
def sha(x):return hashlib.sha256(x).hexdigest()
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def build(out):
 assert __debug__ and not sys.flags.optimize
 raw=s.read_table(INPUT/'parent6.raw.native.tm')
 folds=json.loads((INPUT/'parent6.folds.json').read_text())
 parent,aliases=s.apply_folds(raw,folds)
 assert sha(s.table_text(parent).encode())==json.loads((INPUT/'parent6.receipt.json').read_text())['native_sha256']
 assert len(raw)==404 and len(folds)==8 and len(parent)==388
 raw[164,1]=(1,True,114)
 nopush,_=s.apply_folds(raw,folds)
 # Fixed-control translation of the upstream five cached-Shift edits.
 labels=ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])',(HERE/'reference/PA196/Conjugacy.lean').read_text())[1])
 dense_edits={(37,0):(0,True,11),(37,1):(1,True,101),(127,0):(0,True,133),(127,1):(1,True,20),(133,0):(0,True,120)}
 edits={(labels[q],bit):(w,d,labels[n])for(q,bit),(w,d,n)in dense_edits.items()}
 raw.update(edits)
 child,aliases=s.apply_folds(raw,folds)
 cases=s.check_local_folds(raw,child,aliases,folds)
 assert len(cases['cases'])==32
 assert all(child[q,b]==parent[q,b]for q in c.BOXSTATES for b in(0,1))
 ns={k:tup(v)for k,v in json.loads((INPUT/'parent6.nodes.json').read_text()).items()}
 ns['node163']=('node6','node54')
 c.raw_nodes=lambda:ns
 grammar=c.read_grammar(INPUT/'pa194.grammar.json')
 oldsites,oldins,_=c.source(grammar)
 assert len(oldins)==3776
 ns['node170']=(('node36',('node167','node145')),'node57')
 sites,ins,contracts=c.source(grammar)
 assert len(sites)==3775
 valid=c.validate(child,contracts);assert valid['ok'],valid
 startup=s.startup(child,sites[25][0]);assert startup['steps']==58088
 dense,labels=s.dense_table(child,194)
 out.mkdir(parents=True,exist_ok=True)
 nt=s.table_text(child);dt=s.table_text(dense)
 assert sha(nt.encode())=='9c1daeb54c6e2e402bc5a0405925c1137c19e26280bcf455efe4c91d9a61111d'
 assert sha(dt.encode())=='4bae5b0a698583d97ae8527472dfb627c1cecbba9babd88159fe94c1e3e7dc17'
 for name,text in [('machine.native.tm',nt),('machine.tm',dt),('raw.native.tm',s.table_text(raw))]:(out/name).write_text(text)
 for name,data in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('nodes.json',ns),('folds.json',folds),('local_fold_cases.json',cases),('nopush_parent.instructions.json',oldins)]:dump(out/name,data)
 receipt={'family':'PA194H6','working_states':194,'rows':388,'fixed_controls':135,'AX_readers':67,'simultaneous_folds':8,'local_fold_cases':32,'formula_coefficient':6,'source_sites':len(sites),'source_contracts':len(contracts),'native_edits_from_N6':[[q,b,list(nopush[q,b]),list(child[q,b])]for(q,b)in child if nopush[q,b]!=child[q,b]],'runtime':valid,'startup':startup,'native_sha256':sha(nt.encode()),'dense_sha256':sha(dt.encode()),'kernel_checked':False,'scope':'Finite source binding, every universal physical primitive contract, simultaneous folds, and complete blank startup. Logical calibration is separately an ordinary PA-formalizable proof.'}
 dump(out/'receipt.json',receipt)
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=HERE.parent/'machine');build(p.parse_args().output)
