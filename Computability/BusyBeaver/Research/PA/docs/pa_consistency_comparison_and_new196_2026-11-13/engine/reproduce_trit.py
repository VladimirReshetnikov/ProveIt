#!/usr/bin/env python3
"""Reproduce the source binding and finite closure before context experiments.

Default: independently rebuild the CFG in three ways, rerun the C++ finite
fixed point and closure audit, and verify all saved context binding hashes.
--full: additionally regenerate both radii and rerun the recorded bounded
fold screens. Python3 plus a C++17 compiler is required; --full also uses NumPy.
This is an executable mathematical certificate, not a Lean kernel proof.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
BASE=Path(__file__).resolve().parent
DATA=BASE/'trit_diagonal196'

def need(c,m):
 if not c:raise RuntimeError(m)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def graph_binding(data):
 raw=json.loads((data/'sites.json').read_text())
 syntax=load('trit_source_language',BASE/'inputs/source_language.py')
 syntax.tree(raw)
 ga,checks=syntax.graph_arithmetic(raw);gb=syntax.graph_intervals(raw)
 # The interval resolver returns the graph directly.
 if isinstance(gb,tuple):gb=gb[0]
 need(ga==gb,'arithmetic and interval source CFGs differ')
 fast=load('trit_fast_contexts',BASE/'fast_contexts.py');_,ins=fast.program(raw)
 gc=[];lines=[str(len(ins))]
 for row in ins:
  if row[0]=='halt':g=[['halt'],[]];code=0
  elif row[0]=='jump':g=[['identity'],[row[1]]];code=1
  elif row[0]=='inc':g=[['increment',row[1]],[row[2]]];code=2
  else:g=[['decrement',row[1]],[row[2],row[3]]];code=3
  gc.append(g);lines.append(' '.join(map(str,(code,)+row[1:])))
 need(ga==gc,'path-walking source CFG differs')
 rawgraph=('\n'.join(lines)+'\n').encode()
 need(rawgraph==(data/'source_graph.txt').read_bytes(),'stored CFG differs from source')
 audit=json.loads((data/'invariant_receipt.json').read_text())
 need(hashlib.sha256(rawgraph).hexdigest()==audit['graph_sha256'],'CFG audit digest mismatch')
 need(audit['initial_site']==25 and audit['initial_exact_registers']==[2]+[0]*8,'wrong seed')
 return audit,checks

def run(args,**kw):
 print('+',' '.join(map(str,args)),flush=True)
 return subprocess.run(list(map(str,args)),check=True,**kw)

def main():
 p=argparse.ArgumentParser();p.add_argument('--full',action='store_true');a=p.parse_args()
 audit,checks=graph_binding(DATA)
 with tempfile.TemporaryDirectory(prefix='conpa_trit_')as tmp:
  tmp=Path(tmp);exe=tmp/'joint_trits'
  run(['g++','-O3','-std=c++17',BASE/'joint_trits.cpp','-o',exe])
  result=run([exe,DATA/'source_graph.txt',tmp/'invariant.bin'],capture_output=True,text=True)
  measured=json.loads(result.stdout)
  for key,value in measured.items():need(audit.get(key)==value,('closure receipt mismatch',key))
  need(digest(tmp/'invariant.bin')==audit['bitset_sha256'],'recomputed fixed point digest mismatch')
  need(digest(DATA/'invariant.bin')==audit['bitset_sha256'],'stored fixed point digest mismatch')
  print(json.dumps({'three_CFG_resolvers_agree':True,'successor_premises_checked':checks,'finite_closure_audited':True,**measured},indent=2),flush=True)
  for folder in ['trit_contexts','trit_ones_contexts','trit_ones_wide_contexts']:
   directory=DATA/folder
   if not directory.exists():continue
   receipt=json.loads((directory/'receipt.json').read_text())
   for key,path in [('machine_sha256',DATA/'machine.tm'),('source_sha256',DATA/'sites.json'),('invariant_sha256',DATA/'invariant.bin'),('context_sha256',directory/'source_contexts.txt')]:
    need(receipt[key]==digest(path),('context binding mismatch',folder,key))
   if 'source_graph_sha256'in receipt:need(receipt['source_graph_sha256']==audit['graph_sha256'],'context graph binding differs')
  closing_dirs=[]
  for register in range(3,7):
   directory=BASE/f'trit_diagonal_close{register}'
   if not directory.exists():continue
   closure,_=graph_binding(directory)
   measured=json.loads(run([exe,directory/'source_graph.txt',tmp/f'close{register}.bin'],capture_output=True,text=True).stdout)
   for key,value in measured.items():need(closure.get(key)==value,('closing closure receipt mismatch',register,key))
   need(digest(tmp/f'close{register}.bin')==closure['bitset_sha256'],'closing recomputed fixed point differs')
   need(digest(directory/'invariant.bin')==closure['bitset_sha256'],'closing stored fixed point differs')
   receipt=json.loads((directory/'trit_ones_contexts/receipt.json').read_text())
   for key,path in [('machine_sha256',directory/'machine.tm'),('source_sha256',directory/'sites.json'),('invariant_sha256',directory/'invariant.bin'),('context_sha256',directory/'trit_ones_contexts/source_contexts.txt')]:
    need(receipt[key]==digest(path),('closing context binding differs',register,key))
   need(receipt['base_context_sha256']==digest(DATA/'trit_ones_contexts/source_contexts.txt'),'closing base enclosure binding differs')
   closing_dirs.append(directory)
  differential=None
  if len(closing_dirs)==4:
   module=load('trit_closing_diff',BASE/'closing_diff.py');differential=module.verify()
   need(differential==json.loads((DATA/'closing_differential_receipt.json').read_text()),'closing differential certificate differs')
  if not a.full:
   print('All default source-binding, closure, saved-context, and differential checks passed.');return
  outputs={}
  for radius,folder in[(2,'trit_ones_contexts'),(4,'trit_ones_wide_contexts')]:
   if not(DATA/folder).exists():continue
   out=tmp/folder
   run([sys.executable,BASE/'trit_ones_contexts.py',DATA,out,'--radius',radius])
   need(digest(out/'source_contexts.txt')==digest(DATA/folder/'source_contexts.txt'),'regenerated contexts differ')
   outputs[radius]=out
  screens=[(2,'two_arbitrary_rows.cpp','two'),(2,'three_near_misses.cpp','three'),(2,'offset_helper_five.cpp','offset'),(4,'two_wide_rows.cpp','two'),(4,'offset_helper.cpp','offset')]
  for radius,source,name in screens:
   if radius not in outputs:continue
   archived=DATA/('trit_ones_contexts'if radius==2 else'trit_ones_wide_contexts')
   if not(archived/(name+'_counts.txt')).exists():continue
   binary=tmp/(Path(source).stem);run(['g++','-O3','-std=c++17',BASE/source,'-o',binary])
   out=outputs[radius];command=[binary,DATA/'machine.tm',out/'source_contexts.txt',out/(name+'_results.txt')]
   if source in('two_arbitrary_rows.cpp','three_near_misses.cpp','two_wide_rows.cpp'):command.append('196')
   result=run(command,capture_output=True,text=True)
   need(result.stdout==(archived/(name+'_counts.txt')).read_text(),'bounded search counts differ')
   need((out/(name+'_results.txt')).read_bytes()==(archived/(name+'_results.txt')).read_bytes(),'bounded search result differs')
   print(result.stdout,end='',flush=True)
  if differential is not None:
   binary=tmp/'closing_two_rows';run(['g++','-O3','-std=c++17',BASE/'two_arbitrary_rows.cpp','-o',binary])
   for directory in closing_dirs:
    out=tmp/directory.name
    run([sys.executable,BASE/'trit_ones_contexts.py',directory,out,'--radius','2','--base-contexts',outputs[2]/'source_contexts.txt','--only-sites',*differential['affected_source_sites']])
    archived=directory/'trit_ones_contexts'
    need(digest(out/'source_contexts.txt')==digest(archived/'source_contexts.txt'),'closing regenerated contexts differ')
    result=run([binary,directory/'machine.tm',out/'source_contexts.txt',out/'two_results.txt','196'],capture_output=True,text=True)
    need(result.stdout==(archived/'two_counts.txt').read_text(),'closing search counts differ')
    need((out/'two_results.txt').read_bytes()==(archived/'two_results.txt').read_bytes(),'closing search results differ')
    print(result.stdout,end='',flush=True)
 print('All requested binding, closure, context, and bounded-search checks passed.')
if __name__=='__main__':main()
