#!/usr/bin/env python3
"""Deterministically construct PA194QH6; Python 3.10+, standard library only.

The source and fixed controls are inherited from H6, the AX tree from Q.
No search or external checkout is required. All universal source contracts
are checked by default. This executable certificate is not a Lean proof.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
INPUT=HERE/'inputs'
EXPECTED_DENSE='a48c4729cb35c298c364ba5a7c1d5e489ea3c111f482a93e57338d4c9847d1e9'
def sha(x):return hashlib.sha256(x).hexdigest()
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def build(out,full=True):
 assert __debug__ and not sys.flags.optimize,'Run without Python optimization.'
 fixed_parent=s.read_table(INPUT/'h6.raw.native.tm')
 ns={k:tup(v)for k,v in json.loads((INPUT/'h6.nodes.json').read_text()).items()}
 assert ns['node163']==('node6','node54')
 assert ns['node170']==(('node36',('node167','node145')),'node57')
 inc=('leaf','inc',1)
 assert ns['node61']==((inc,'node60'),(inc,'node60'))
 c.machine=lambda:(fixed_parent,[])
 c.raw_nodes=lambda:ns
 c.MACROS[(inc,inc)]=99
 c.MACROS[((inc,inc),(inc,inc))]=190
 grammar=c.read_grammar(INPUT/'q.grammar.json')
 raw,index,shape=c.build(grammar)
 assert len(raw)==404 and len(shape)==67
 assert {k:v for k,v in raw.items()if k[0]<1300}=={k:v for k,v in fixed_parent.items()if k[0]<1300}
 folds=json.loads((INPUT/'q.folds.json').read_text())
 assert len(folds)==7
 folds.append([41,99,[[0,False,30],[1,False,2040]]])
 child,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,child,aliases,folds)
 assert len(local['cases'])==32
 assert all(child[q,b]==fixed_parent[q,b]for q in c.BOXSTATES for b in(0,1))
 sites,instructions,contracts=c.source(grammar)
 assert len(sites)==3775 and len(contracts)==4876
 valid=c.validate(child,contracts)if full else None
 if full:assert valid['ok'],valid
 startup=s.startup(child,sites[25][0]);assert startup['steps']==58088
 dense,labels=s.dense_table(child,194)
 native_text=s.table_text(child);dense_text=s.table_text(dense)
 assert sha(dense_text.encode())==EXPECTED_DENSE
 out.mkdir(parents=True,exist_ok=True)
 for name,table in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:(out/name).write_text(s.table_text(table))
 for name,data in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',instructions),('nodes.json',ns),('folds.json',folds),('local_fold_cases.json',local)]:dump(out/name,data)
 receipt={'family':'PA194QH6','working_states':194,'rows':388,'fixed_controls':135,'AX_readers':67,'raw_states':202,'simultaneous_folds':8,'local_fold_cases':32,'formula_coefficient':6,'source_sites':len(sites),'source_contracts':len(contracts),'arithmetic_box_rows_unchanged_from_H6':True,'fixed_rows_unchanged_from_H6':True,'emitter':'Q: exchanged universal-distribution premises','MP_success':'(b,w,b,0), b=d+x','Shift_test':'h=1','runtime':valid,'startup':startup,'native_sha256':sha(native_text.encode()),'dense_sha256':sha(dense_text.encode()),'kernel_checked':False,'scope':'Ordinary mathematical PA-provability argument with executable source, physical, fold and complete-startup certificates. No end-to-end Lean/Rocq endpoint is claimed.'}
 dump(out/'receipt.json',receipt)
 print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--output',type=Path,default=HERE.parent/'machine')
 p.add_argument('--skip-runtime',action='store_true',help='Skip only the construction universal runtime; this is not a full verification.')
 args=p.parse_args();build(args.output,not args.skip_runtime)
