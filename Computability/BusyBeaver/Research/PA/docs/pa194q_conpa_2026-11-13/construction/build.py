from pathlib import Path
import sys,json,itertools,hashlib,argparse
PACKAGE=Path(__file__).resolve().parent.parent
BASE=PACKAGE
sys.path.insert(0,str(BASE/'construction'))
import compiler as c,baseline_tools as b
orig=c.raw_nodes
cached=b.read_table(BASE/'construction/inputs/pa194C.native.tm')
def nodes():
 ns=orig();ns['node163']=('node6','node147');ns['node170']=(('node36',('node167','node145')),'node57');return ns
c.raw_nodes=nodes;c.machine=lambda:(cached,[])
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190


def main(path,out):
 path=Path(path);out=Path(out);out.mkdir(exist_ok=True)
 # Freeze exact grammar before any long checks.
 data=path.read_bytes();(PACKAGE/'evidence/grammar.used.json').write_bytes(data)
 t=c.read_grammar(PACKAGE/'evidence/grammar.used.json');raw,index,shape=c.build(t)
 folds=json.loads((PACKAGE/'construction/folds.json').read_text())
 child,aliases=b.apply_folds(raw,folds)
 local=b.check_local_folds(raw,child,aliases,folds)
 assert len(raw)==402 and len(shape)==67 and len(folds)==7
 sites,ins,contracts=c.source(t);count=len(child)//2
 print('raw',len(raw)//2,'folds',len(folds),'states',count,'sites',len(sites),flush=True)
 v=c.validate(child,contracts);print(v,flush=True);assert v['ok']
 seed=b.startup(child,sites[25][0]);dense,labels=b.dense_table(child,count)
 for name,table in [('pa194q.native.tm',child),('pa194q.tm',dense),('unfolded201.native.tm',raw)]: (out/name).write_text(b.table_text(table))
 for name,data in [('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('labels.json',labels),('folds.json',folds),('local_cases.json',local),('macro_word.json',b.word(b.expanded(t)))]:
  (out/name).write_text(json.dumps(data,indent=2)+'\n')
 r={'states':count,'raw_states':len(raw)//2,'fixed_states':134,'reader_states':len(shape),'folds':len(folds),'sites':len(sites),'contracts':len(contracts),'validation':v,'seed':seed,'sha256':hashlib.sha256((out/'pa194q.tm').read_bytes()).hexdigest()}
 (PACKAGE/'evidence/construction.json').write_text(json.dumps(r,indent=2)+'\n')
 assert r['sha256']=='48e98b5504dc5b3f20a2d040cb54ed1c96bee4c5e32ea27ae98ffada4dce7ea1'
 print(json.dumps(r,indent=2),flush=True)
if __name__=='__main__':main(PACKAGE/'construction/grammar.json',PACKAGE/'machine')
