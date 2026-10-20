#!/usr/bin/env python3
"""Reject malformed source proofs and runtime evidence on temporary copies."""
from pathlib import Path
import argparse,copy,importlib.util,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'portable'))
import check_runtime as runtime
spec=importlib.util.spec_from_file_location('source_proof',ROOT/'portable/source/reconstruct_source.py')
source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
 ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--vendor',type=Path,required=True);ap.add_argument('--runtime',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 old=json.loads((a.baseline/'machine/sites219.json').read_text());sites=json.loads((ROOT/'machine/sites218.json').read_text());reference=source.graph_arithmetic(old)[0];results=[]
 def equal(rows):
  source.tree(rows);g=source.graph_arithmetic(rows)[0]
  source.require(g==source.graph_intervals(rows),'Independent CFG mismatch')
  source.require([x[1:]for x in rows]==[x[1:]for x in old],'Primitive ordinal word changed')
  source.require(g==reference,'All-natural ordinal step relation changed')
 def rejects(name,call):
  try:call()
  except(AssertionError,ValueError,KeyError,IndexError)as e:results.append(dict(name=name,status='REJECTED',exception=type(e).__name__))
  else:raise AssertionError('Accepted negative control: '+name)
 equal(sites)
 bad=copy.deepcopy(sites);i=next(i for i,x in enumerate(bad)if x[1]=='CI');bad[i][2]=(bad[i][2]+1)%9
 rejects('changed_register_operation',lambda:equal(bad))
 bad=copy.deepcopy(sites);i=next(i for i,x in enumerate(bad)if x[1]=='CC');bad[i][2]+=1
 rejects('changed_control_argument',lambda:equal(bad))
 bad=copy.deepcopy(sites);bad[1][0]=bad[0][0]
 rejects('duplicate_source_address',lambda:equal(bad))
 bad=copy.deepcopy(sites);bad.pop()
 rejects('omitted_source_leaf',lambda:equal(bad))
 table=runtime.read_table(ROOT/'machine/k218.normalized.tm');sp=runtime.SPECS['candidate218']
 with tempfile.TemporaryDirectory(prefix='k218-negative-')as temporary:
  out=Path(temporary)/'runtime';out.mkdir()
  def reset():
   for filename in('runtime.json','cases.json','startup.json','canonical.tm'):shutil.copy2(a.runtime/filename,out/filename)
  def cases(label,edit):
   reset();p=out/'cases.json';x=json.loads(p.read_text());edit(x);dump(p,x)
   rejects(label,lambda:runtime.audit(table,sites,sp,out,a.vendor))
  cases('omitted_generic_case',lambda x:x.pop())
  cases('duplicated_generic_case',lambda x:x.__setitem__(1,copy.deepcopy(x[0])))
  cases('nonpositive_duration',lambda x:x[0]['duration'].__setitem__(0,0))
  reset();p=out/'runtime.json';x=json.loads(p.read_text());x['block_schemas'][0]['trace'][0][1][2]^=1;dump(p,x)
  rejects('false_exact_table_block',lambda:runtime.audit(table,sites,sp,out,a.vendor))
  reset();p=out/'runtime.json';x=json.loads(p.read_text());x['directly_used_rows'].pop();dump(p,x)
  rejects('omitted_literal_row_coverage',lambda:runtime.audit(table,sites,sp,out,a.vendor))
  reset();p=out/'startup.json';x=json.loads(p.read_text());x['startup']['steps']+=1;dump(p,x)
  rejects('wrong_complete_startup_duration',lambda:runtime.audit(table,sites,sp,out,a.vendor))
  reset();p=out/'startup.json';x=json.loads(p.read_text());x['startup']['ones'][0]-=1;dump(p,x)
  rejects('wrong_complete_tape_support_same_cardinality',lambda:runtime.audit(table,sites,sp,out,a.vendor))
  for filename,args in [('check_runtime.py',['--help']),('reproduce.py',['--output-dir',str(Path(temporary)/'optimized-output')])]:
   proc=subprocess.run([sys.executable,'-O',str(ROOT/'portable'/filename),*args],capture_output=True,text=True)
   assert proc.returncode!=0 and 'Assertions must' in proc.stdout+proc.stderr,(filename,proc.returncode,proc.stderr)
   results.append(dict(name='optimization_rejected_'+filename,status='REJECTED',returncode=proc.returncode))
 dump(a.output,dict(status='ALL_K218_NEGATIVE_CONTROLS_REJECTED',count=len(results),controls=results,scope='Checker-boundary tests only, not substitutes for source bisimulation or unbounded runtime proof.'))
 print('ALL_K218_NEGATIVE_CONTROLS_REJECTED',len(results))
if __name__=='__main__':main()
