#!/usr/bin/env python3
"""Read retained search evidence; no machine, checker or search execution."""
from pathlib import Path
import argparse,collections,gzip,hashlib,json,re
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--output',type=Path,required=True);args=a.parse_args()
 if args.output.exists():raise FileExistsError(args.output)
 checks=0;runs=[];inputs=json.loads((P/'inputs.json').read_text())
 descriptors=inputs['seeds']+[inputs['decoder_allocation'],inputs['universal_checker']]
 for d in descriptors:
  assert sha((P/d['path']).resolve())==d['sha256'];checks+=1
 for name,source in [('run1','search.py'),('run2','search_v2.py'),('run3','search_v3.py'),('helpers-run1','search_helpers.py')]:
  d=P/'results'/name;r=json.loads((d/'result.json').read_text())
  assert r['status']=='COMPLETE_BOUNDED_SEARCH' and r['hits']==[]
  assert sha(d/'search.py')==sha(P/source)==r['search_sha256']
  assert sha(d/'check_joint_fold.py')==inputs['universal_checker']['sha256']
  assert json.loads((d/'inputs.json').read_text())==inputs
  assert sha(d/'rejections.jsonl.gz')==r['rejection_stream_sha256'];checks+=5
  totals=collections.Counter();families=collections.Counter();pairs=collections.defaultdict(set);reasons=collections.Counter();count=0
  with gzip.open(d/'rejections.jsonl.gz','rt') as f:
   for line in f:
    row=json.loads(line);count+=1
    assert row['id']==count and row['stage']=='bounded_filter'
    assert row['keep']<row['drop'] and row['keep']!=0
    assert row['witness']['radius']==r.get('filter_radius',3) and row['witness']['fuel']==r.get('filter_fuel',9)
    totals[row['seed']]+=1;families[row['seed'],row['family']]+=1;pairs[row['seed']].add((row['keep'],row['drop']));reasons[row['witness']['reason']]+=1;checks+=3
  assert count==r['attempted'];checks+=1
  for s in r['seeds']:
   assert totals[s['seed']]==s['attempted']==s['filter_rejections']
   assert len(pairs[s['seed']])==s['pairs']
   assert s['universal_pass']==s['universal_rejections']==0
   assert all(families[s['seed'],k]==v for k,v in s['families'].items());checks+=4
  runs.append({'name':name,'result_sha256':sha(d/'result.json'),'rejections':count,'reasons':dict(reasons),'source_sha256':r['search_sha256']})
 for name,source in [('controls-v2.json','control_checks.py'),('controls-v3.json','control_checks_v3.py')]:
  r=json.loads((P/'results'/name).read_text());assert r['source_sha256']==sha(P/source) and r['status']=='SYNTHETIC_NONTRIVIAL_MERGE_CONTROLS_PASS';checks+=1
 for target in re.findall(r'\]\(([^)]+)\)',(P/'README.md').read_text()):
  assert (P/target.split('#')[0]).resolve().exists(),target;checks+=1
 out={'status':'RECORDED_EVIDENCE_METADATA_PASS','checks':checks,'runs':runs,'role':'Search author reviewing retained metadata; not independent mathematical review. No search/checker/simulator executed by this reader.','script_sha256':sha(Path(__file__))}
 args.output.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'status':out['status'],'checks':checks,'runs':len(runs)}))
if __name__=='__main__':main()
