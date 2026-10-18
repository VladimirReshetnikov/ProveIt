#!/usr/bin/env python3
"""Stage exact reviewed QT244/combined243 candidate files outside the repository.

No maintained writes, Git mutation, simulation, supplied checker or compiler.
Root separately reviews and installs the emitted explicit map.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json
BASE='Computability/BusyBeaver/Research/ZFC'
def require(b,msg):
 if not b:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--inputs',type=Path,default=Path(__file__).with_name('candidate-inputs.json'));ap.add_argument('--inputs-sha',required=True);a=ap.parse_args();r=a.repo.resolve();o=a.output.resolve()
 require(not o.exists() and o!=r and r not in o.parents,'Fresh external output required');require(sha(a.inputs)==a.inputs_sha,'Changed candidate input map');m=json.loads(a.inputs.read_text());require(m['status']=='FROZEN_CANDIDATE_PROMOTION_PROPOSAL','Wrong scope');require(m['no_complete_lean_consistency_endpoint'] and m['no_internal_PA_endpoint'],'Scope boundary')
 for p in m['required_current']:
  require(sha(r/p['path'])==p['sha256'],'Current prerequisite changed: '+p['path'])
 actual=m['actual']
 qt=json.loads(Path(actual['rotation_primary']).read_text());ex=json.loads(Path(actual['combined_expanded']).read_text());quick=json.loads(Path(actual['combined_quick']).read_text())
 require(qt['status']=='PASS_ROOT_ROTATION244_PRIMARY_REPLAY' and len(qt['jobs'])==7 and qt['cases']==8390 and qt['symbolic_rules']==2312438,'QT primary outcome')
 require(all(x['returncode']==0 and not x['timeout'] for x in qt['jobs']),'QT command failure')
 require(ex['status']=='PASS_COMBINED243_EXPANDED_RUNTIME' and ex['counts']=={'cases':8390,'symbolic_rules':2314868} and ex['rows_covered']==485 and ex['unused_rows']==[[27,1]],'Combined expanded scope')
 require(quick['status']=='PASS_COMBINED243_BLANK_AFFINE_LITERAL' and quick['blank_steps']==407967 and quick['cases']==8390 and quick['literal_steps']==6473394,'Combined quick scope')
 for e in [ex,quick]:
  require(e['before']==e['after'],'Combined input changed');require(all(x['exit_code']==0 and not x['timeout'] for x in e['commands']),'Combined command failure')
  for p,h in e['before'].items():require(sha(p)==h,'Combined selected input changed: '+p)
 selected=set()
 for row in m['files']:
  p=Path(row['source']);t=PurePosixPath(row['target']);require(not t.is_absolute() and '..' not in t.parts and '\\' not in str(t),'Unsafe destination');require(any(str(t).startswith(BASE+'/'+name+'/') for name in ['candidate-rotation244','candidate-combined243']),'Unexpected namespace');require(str(t) not in selected,'Duplicate destination');selected.add(str(t));require(not (r/str(t)).exists() and not (r/str(t)).is_symlink(),'Destination already exists');require(p.is_file() and sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],'Changed source: '+str(p))
 o.mkdir();out=[]
 for row in m['files']:
  p=o/'files'/row['target'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(Path(row['source']).read_bytes());require(sha(p)==row['sha256'],'Staged mismatch');out.append(dict(row,source=str(p)))
 for row in m['files']:require(sha(row['source'])==row['sha256'],'Input changed during staging')
 require(sha(a.inputs)==a.inputs_sha,'Map changed during staging')
 result={'status':'STAGED_FOR_ROOT_REVIEW_NOT_INSTALLED','files':out,'input_map_sha256':a.inputs_sha,'helper_sha256':sha(__file__),'maintained_mutations':False,'supplied_execution':False,'scopes':m['scopes']};(o/'publication-map.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'files':len(out),'map':str(o/'publication-map.json')}))
if __name__=='__main__':main()
