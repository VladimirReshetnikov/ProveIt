#!/usr/bin/env python3
"""Compose the G explicit-binder AX with H's cached-only Shift controller.

The named inputs and physical engines are inherited from the pinned ProveIt
PA194G and H packets; this composition is new within the recounted corpus.
No absolute iPRA/PA-consistency calibration is asserted by this builder.
"""
import argparse,hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
import support
def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t
INC=('leaf','inc',1)
def normal(t):
 if t=='node60':return INC,INC
 if t=='node61':return (INC,INC),(INC,INC)
 return tuple(map(normal,t)) if c.isnode(t) else t
def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def main(out,full):
 assert __debug__ and not sys.flags.optimize
 nodes0={k:tup(v) for k,v in json.loads((ROOT/'inputs/nodes.json').read_text()).items()}
 assert nodes0['node163']==('node6','node54')
 nodes=dict(nodes0)
 nodes['node170']=(('node36',('node167','node145')),'node57')
 base=support.read_table(ROOT/'inputs/raw.native.tm')
 edits={(38,0):(0,True,11),(38,1):(1,True,122),(214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}
 before={k:base[k] for k in edits}
 rows0=dict(base);rows0.update(edits)
 c.machine=lambda:(rows0,[]);c.raw_nodes=lambda:nodes
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 grammar=normal(c.read_grammar(ROOT/'inputs/grammar.json'))
 raw,_,shape=c.build(grammar)
 folds=json.loads((ROOT/'inputs/folds.json').read_text())
 rows,aliases=support.apply_folds(raw,folds)
 local=support.check_local_folds(raw,rows,aliases,folds)
 assert len(raw)==402 and len(shape)==67 and len(rows)==388
 assert all(rows[q,b]==base[q,b] for q in c.BOXSTATES for b in (0,1))
 sites,ins,contracts=c.source(grammar)
 startup=support.startup(rows,sites[25][0])
 dense,labels=support.dense_table(rows,194)
 out.mkdir(parents=True,exist_ok=True)
 for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
  (out/name).write_text(support.table_text(table))
 for name,obj in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]),('instructions.json',ins),('nodes.json',nodes),('folds.json',folds),('local_folds.json',local),('startup.json',startup)]:dump(out/name,obj)
 runtime=c.validate(rows,contracts) if full else None
 if full:assert runtime['ok'],runtime
 receipt=dict(name='PA194GH',states=194,rows=388,raw_controls=len(raw)//2,fixed_controls=len(raw)//2-len(shape),readers=len(shape),folds=len(folds),source_sites=len(sites),source_outcomes=len(contracts),startup_steps=startup['steps'],runtime=runtime,edits=[[q,b,before[q,b],edits[q,b]] for q,b in edits],dense_sha256=hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest(),native_sha256=hashlib.sha256((out/'machine.native.tm').read_bytes()).hexdigest(),source_graph='G explicit AX binder with H cache-only Shift',absolute_ipra_calibration=False,kernel_checked=False)
 dump(out/'receipt.json',receipt);print(json.dumps(receipt,indent=2),flush=True)
 return receipt
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=pathlib.Path,default=ROOT/'machine');ap.add_argument('--quick',action='store_true');a=ap.parse_args();main(a.output,not a.quick)
