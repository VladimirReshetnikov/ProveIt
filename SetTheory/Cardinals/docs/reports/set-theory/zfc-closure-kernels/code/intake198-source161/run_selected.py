#!/usr/bin/env python3
"""Own portable Source161 selected-leaf runner; no wrapper/ancestor/full replay."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time,traceback
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def read(p):return json.loads(p.read_bytes())
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 a.out=a.out.resolve();a.out.mkdir(parents=True,exist_ok=False);a.packet=a.packet.resolve();pins=read(Path(__file__).with_name('selected-inputs.json'))
 actual={'status':'FAIL','scope':'Only new construction, independent source graph comparison, and one-case wrong-CB detection. No manifest/ancestor/full runtime/blank execution.','runner_sha256':sha(Path(__file__)),'jobs':[]}
 try:
  assert all(sha(a.packet/r)==h for r,h in pins.items())
  packet=a.out/'packet';shutil.copytree(a.packet,packet);logs=a.out/'logs';logs.mkdir();outputs=a.out/'outputs';outputs.mkdir()
  before={r:sha(packet/r)for r in pins};assert before==pins;actual['before']=before
  specs=[('reconstruct',['code/reconstruct.py','--parent','reference/partial216','--output',str(outputs/'rebuilt')]),
   ('source',['code/audit_source.py','--reference','reference/permuted216/sites210.json','--candidate','source/sites215.json','--out',str(outputs/'source.json')]),
   ('negative-control',['code/negative_control.py','--table','machine/k215.native.tm','--sites','source/sites215.json','--out',str(outputs/'negative-control.json')])]
  for name,args in specs:
   argv=[sys.executable,'-B',*args];started=time.monotonic();row={'name':name,'argv':argv,'cwd':str(packet),'wall_cap_seconds':60}
   with(logs/(name+'.stdout')).open('wb')as out,(logs/(name+'.stderr')).open('wb')as err:
    try:p=subprocess.run(argv,cwd=packet,stdout=out,stderr=err,timeout=60);row.update(returncode=p.returncode,timed_out=False)
    except subprocess.TimeoutExpired:row.update(returncode=None,timed_out=True)
   row['elapsed_seconds']=time.monotonic()-started;row['stdout_sha256']=sha(logs/(name+'.stdout'));row['stderr_sha256']=sha(logs/(name+'.stderr'));actual['jobs'].append(row)
   assert row['returncode']==0 and not row['timed_out'],name
   if name=='reconstruct':
    r=read(outputs/'rebuilt/reconstruction.json');assert r['status']=='PASS_EXACT_K215_RECONSTRUCTION'and r['working_states']==215 and r['rows']==430 and r['source_leaves']==4751 and r['changed_retained_rows']==36 and r['deleted_states']==[185]
    for rel,dst in [('machine/k215.native.tm','k215.native.tm'),('machine/k215.tm','k215.tm'),('source/sites215.json','sites215.json'),('machine/canonicalization.json','canonicalization.json')]:assert(packet/rel).read_bytes()==(outputs/'rebuilt'/dst).read_bytes()
   elif name=='source':
    r=read(outputs/'source.json');assert r['status']=='PASS'and len(r['inputs'])==2 and r['identical_paths']==346
    for item,depth in zip(r['inputs'],[44,47]):assert (item['primitives'],item['dag_nodes'],item['guarded_edges'],item['guarded_cases_including_halt'],item['maximum_depth'],item['maximum_zero_run'])==(4751,202,6175,6176,depth,6)
    assert [x['sha256']for x in r['inputs']]==[pins['reference/permuted216/sites210.json'],pins['source/sites215.json']]
   else:
    r=read(outputs/'negative-control.json');assert r['status']=='PASS_MUTATION_REJECTED'and r['baseline_case']=='PASS'and r['site_index']==4697 and r['site']==['11010011','CB',1]
    assert r['old_native_row']==[135,1,0,-1,302]and r['bad_native_row']==[135,1,0,-1,10]
    assert r['failure']==read(packet/'evidence/replay-negative-control.json')['failure']
   row['semantic_gate']='PASS';print('PASS',name,round(row['elapsed_seconds'],4),flush=True)
  actual['after']={r:sha(packet/r)for r in pins};assert actual['after']==before
  actual['outputs']={str(p.relative_to(outputs)):sha(p)for p in outputs.rglob('*')if p.is_file()};actual['status']='PASS_SELECTED_SOURCE161_LEAVES'
 except Exception as e:
  actual['exception']={'type':type(e).__name__,'message':str(e)};(a.out/'failure.log').write_text(traceback.format_exc())
 finally:dump(a.out/'actual.json',actual)
 print(actual['status'],flush=True)
 if actual['status']!='PASS_SELECTED_SOURCE161_LEAVES':raise SystemExit(1)
if __name__=='__main__':main()
