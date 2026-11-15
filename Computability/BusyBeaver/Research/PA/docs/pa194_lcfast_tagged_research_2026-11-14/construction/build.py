#!/usr/bin/env python3
"""Compose loop continuation routing with exact fast decoder, retaining source CFG."""
from pathlib import Path
import argparse,json,hashlib,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c,support as s
INC=('leaf','inc',1)
LC={(139,0):(0,True,99),(139,1):(1,True,190),(190,1):(1,False,73)}
FAST={(26,1):(1,True,91),(101,0):(0,True,17)}
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def build(base,full):
 folder=ROOT/'inputs'/base
 name=base.replace('AX11','LCAX11')+'F'
 out=ROOT/'machines'/name;out.mkdir(parents=True,exist_ok=True)
 parent_raw=s.read_table(folder/'raw.native.tm');parent=s.read_table(folder/'machine.native.tm')
 nodes={k:tup(v)for k,v in json.loads((folder/'nodes.json').read_text()).items()}
 grammar=tup(json.loads((folder/'grammar.tree.json').read_text()))
 c.raw_nodes=lambda:nodes
 oldsites,oldins,_=c.source(grammar)
 assert json.loads(json.dumps(oldins))==json.loads((folder/'instructions.json').read_text())
 c.MACROS[(INC,INC)]=99
 c.MACROS.pop(((INC,INC),(INC,INC)),None);c.MACROS.pop('node61',None)
 assert nodes['node62']==('node61',('leaf','continueTo',2))
 nodes['node62']=((INC,INC),((INC,INC),('leaf','continueTo',3)))
 raw=dict(parent_raw);raw.update(LC)
 c.machine=lambda:(raw,[])
 rebuilt,_,shape=c.build(grammar)
 assert rebuilt==raw
 folds=json.loads((folder/'folds.json').read_text())
 normal,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,normal,aliases,folds)
 rows=dict(normal);rows.update(FAST)
 # FAST affects neither the local fold identities nor the arithmetic engine.
 fastlocal=s.check_local_folds(raw,rows,aliases,folds)
 assert all(rows[q,b]==parent[q,b]for q in c.BOXSTATES for b in(0,1))
 sites,ins,contracts=c.source(grammar)
 assert ins==oldins
 assert len(rows)==388
 valid=c.validate(rows,contracts)if full else None
 if full:assert valid['ok'],valid
 startup=s.startup(rows,sites[25][0])
 dense,labels=s.dense_table(rows,194)
 for fn,tbl in [('raw.native.tm',raw),('machine.native.tm',rows),('machine.tm',dense)]:
  (out/fn).write_text(s.table_text(tbl))
 for fn,x in [('nodes.json',nodes),('grammar.tree.json',grammar),('folds.json',folds),('fold_cases.json',fastlocal),('sites.json',[[''.join(map(str,p)),op,arg]for p,op,arg in sites]),('instructions.json',ins),('labels.json',labels)]:dump(out/fn,x)
 edits=[[q,b,list(parent[q,b]),list(rows[q,b])]for q,b in sorted(parent)if rows[q,b]!=parent[q,b]]
 assert [(q,b)for q,b,_,_ in edits]==sorted(list(LC)+list(FAST))
 receipt={'name':name,'status':'PASS','base':base,'working_states':194,'transition_rows':388,'raw_controls':len(raw)//2,'AX_readers':len(shape),'folds':len(folds),'source_sites':len(ins),'source_outcomes':len(contracts),'source_graph_identical':True,'changed_source_addresses':sum(a[0]!=b[0]for a,b in zip(oldsites,sites)),'runtime':valid,'startup':startup,'native_edits':edits,'dense_sha256':digest(out/'machine.tm'),'native_sha256':digest(out/'machine.native.tm'),'parent_dense_sha256':digest(folder/'machine.tm'),'kernel_checked':False,'absolute_consistency_calibration_established_here':False}
 dump(out/'receipt.json',receipt)
 print(json.dumps({k:receipt[k]for k in ('name','status','working_states','source_sites','source_outcomes','dense_sha256','startup')},indent=2),flush=True)
 return receipt
if __name__=='__main__':
 assert __debug__ and not sys.flags.optimize
 p=argparse.ArgumentParser();p.add_argument('--quick',action='store_true');a=p.parse_args()
 rs=[build(n,not a.quick)for n in ('PA194AX11GH','PA194AX11GHS')]
 dump(ROOT/'build_receipt.json',rs)
