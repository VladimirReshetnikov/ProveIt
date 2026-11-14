#!/usr/bin/env python3
"""Construct QH5 from QH6 by a fully bound coefficient-five source change."""
from pathlib import Path
import argparse, hashlib, json, sys
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
INPUT=HERE/'inputs'
INC=('leaf','inc',1)
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def paths(grammar,ns,target):
 out=[]
 def walk(t,p):
  if isinstance(t,str):
   if t==target:out.append(p)
   return walk(grammar if t=='x67' else ns[t],p)
  if c.isnode(t):walk(t[0],p+(0,));walk(t[1],p+(1,))
 walk('node172',());return out

def bind_source(grammar,oldns,newns,oldsites,oldins,sites,ins):
 oldpaths=paths(grammar,oldns,'node61');newpaths=paths(grammar,newns,'node61')
 assert oldpaths==newpaths and len(oldpaths)==61
 cp=paths(grammar,oldns,'node65')
 assert cp==paths(grammar,newns,'node65') and [p+(1,1,1,0) for p in cp]==oldpaths
 blocks=[];oldremoved=set();newremoved=set();entries={}
 cons_prefix=[('dec',2,8,1),('inc',7,2),('dec',6,4,3),('jump',7),('dec',7,7,5),('inc',6,6),('jump',4),('jump',0),('dec',7,11,9),('inc',2,10),('jump',8),('dec',1,15,12),('inc',7,13),('inc',6,14),('jump',11),('dec',6,21,16),('inc',7,17),('dec',6,20,18),('inc',1,19),('jump',17),('jump',11)]
 for p in oldpaths:
  oi=[i for i,(q,op,arg)in enumerate(oldsites) if q[:len(p)]==p]
  ni=[i for i,(q,op,arg)in enumerate(sites) if q[:len(p)]==p]
  assert oi==list(range(oi[0],oi[0]+6)) and ni==list(range(ni[0],ni[0]+5))
  for ids,code in ((oi,oldins),(ni,ins)):
   assert all(code[i]==('inc',1,i+1) for i in ids)
   start,end=ids[0],ids[-1]+1
   base=start-22
   prefix=[]
   for row in code[base:base+21]:
    prefix.append(row[:2]+tuple(v-base for v in row[2:]) if row[0] in ('inc','dec') else ('jump',row[1]-base))
   assert prefix==cons_prefix
   assert code[start-1]==('dec',7,end+1,start)
   assert code[end]==('jump',start-1)
  oldremoved.update(oi);newremoved.update(ni);entries[oi[0]]=ni[0]
  blocks.append({'path':''.join(map(str,p)),'old_start':oi[0],'new_start':ni[0],'old_length':6,'new_length':5})
 oldkept=[i for i in range(len(oldins)) if i not in oldremoved]
 newkept=[i for i in range(len(ins)) if i not in newremoved]
 assert len(oldkept)==len(newkept)==3409
 relocate=dict(zip(oldkept,newkept));relocate.update(entries)
 def targets(row):return row[2:] if row[0] in ('inc','dec') else row[1:] if row[0]=='jump' else ()
 def projected(row):
  if row[0] in ('inc','dec'):return row[:2]+tuple(relocate[x] for x in row[2:])
  if row[0]=='jump':return ('jump',relocate[row[1]])
  return row
 for i,j in zip(oldkept,newkept):assert projected(oldins[i])==ins[j]
 for code,removed,starts in ((oldins,oldremoved,set(entries)),(ins,newremoved,set(entries.values()))):
  for i,row in enumerate(code):
   if i not in removed:assert all(t not in removed or t in starts for t in targets(row))
 assert relocate[25]==25 and oldsites[25][0]==sites[25][0]
 return {'from_coefficient':6,'to_coefficient':5,'occurrences':61,'unchanged_primitive_sites':3409,
         'all_61_constructors_have_exact_unpair_pair_prefix':True,'only_formula_constructor_loop_bodies_change':True,'no_external_entries_to_body_interior':True,
         'all_resolved_outside_successors_preserved':True,'same_seed_site':25,'blocks':blocks}

def build(out,full=True):
 assert __debug__ and not sys.flags.optimize
 oldraw=s.read_table(INPUT/'qh6.raw.native.tm')
 oldns={k:tup(v)for k,v in json.loads((INPUT/'qh6.nodes.json').read_text()).items()}
 assert oldns['node61']==((INC,'node60'),(INC,'node60'))
 assert oldns['node163']==('node6','node54')
 assert oldns['node170']==(('node36',('node167','node145')),'node57')
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 grammar=c.read_grammar(INPUT/'q.grammar.json')
 c.raw_nodes=lambda:oldns
 oldsites,oldins,oldcontracts=c.source(grammar)
 assert len(oldsites)==3775 and len(oldcontracts)==4876
 c.machine=lambda:(oldraw,[])
 rebuilt,_,shape=c.build(grammar)
 assert rebuilt==oldraw and len(shape)==67
 raw=dict(oldraw)
 assert raw[190,1]==(1,True,330)
 raw[190,1]=(1,True,99)
 ns=dict(oldns);ns['node61']=((INC,'node60'),'node60')
 c.raw_nodes=lambda:ns
 sites,ins,contracts=c.source(grammar)
 assert len(sites)==3714 and len(contracts)==4815
 binding=bind_source(grammar,oldns,ns,oldsites,oldins,sites,ins)
 folds=json.loads((INPUT/'q.folds.json').read_text())+[[41,99,[[0,False,30],[1,False,2040]]]]
 child,aliases=s.apply_folds(raw,folds);local=s.check_local_folds(raw,child,aliases,folds)
 assert len(local['cases'])==32
 assert all(child[q,b]==oldraw[q,b] for q in c.BOXSTATES for b in(0,1))
 result=c.validate(child,contracts) if full else None
 if full:assert result['ok'],result
 startup=s.startup(child,sites[25][0]);assert startup['steps']==58088
 dense,labels=s.dense_table(child,194)
 out.mkdir(exist_ok=True,parents=True)
 for name,table in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:
  (out/name).write_text(s.table_text(table))
 for name,data in [('labels.json',labels),('nodes.json',ns),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('local_fold_cases.json',local),('source_binding.json',binding)]:dump(out/name,data)
 receipt={'family':'PA194QH5','working_states':194,'rows':388,'fixed_controls':135,'AX_readers':67,
          'raw_states':202,'folds':8,'local_cases':32,'source_sites':len(sites),'source_outcomes':len(contracts),
          'coefficient':5,'runtime':result,'startup':startup,
          'native_sha256':hashlib.sha256((out/'machine.native.tm').read_bytes()).hexdigest(),
          'dense_sha256':hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest(),
          'change_from_QH6':{'native_control':190,'read':1,'old':[1,'R',330],'new':[1,'R',99]},
          'kernel_checked':False}
 assert receipt['dense_sha256']=='94c85547b3edd0df0a441d45bf22abb52711f2b27cc9e680999232285757dba5'
 assert receipt['native_sha256']=='45c649af2600c2cfa8bbb07ce2a674e07945d985af6c9fc8aaa8563df1225c05'
 dump(out/'receipt.json',receipt);print(json.dumps(receipt,indent=2));return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=HERE.parent/'machine');p.add_argument('--skip-runtime',action='store_true');a=p.parse_args();build(a.output,not a.skip_runtime)
