"""Read saved feature evidence only. Does not invoke proof tools or assert full phase6 success."""
from pathlib import Path,PurePosixPath
import argparse,json,hashlib,tarfile,re
BAD={'.olean','.ilean','.o','.so','.a','.pyc','.vo','.vos','.vok','.glob','.exe'}
sha=lambda b:hashlib.sha256(b).hexdigest()
def review(directory):
 summary=json.loads((directory/'summary.json').read_text());idx=json.loads((directory/'index.json').read_text());raw=(directory/'evidence.tar.gz').read_bytes()
 assert sha(raw)==summary['archive_sha256']and sha((directory/'index.json').read_bytes())==summary['index_sha256']
 data={}
 with tarfile.open(directory/'evidence.tar.gz','r:gz')as t:
  for m in t.getmembers():
   p=PurePosixPath(m.name);assert m.isfile()and not p.is_absolute()and '..'not in p.parts
   assert p.suffix not in BAD and not {'objects','__pycache__'}&set(p.parts)
   assert m.name not in data and m.name in idx;data[m.name]=t.extractfile(m).read();data[m.name].decode('utf-8')
   assert len(data[m.name])==idx[m.name]['bytes']and sha(data[m.name])==idx[m.name]['sha256']
 assert data.keys()==idx.keys()and len(data)==summary['members']
 assert sum(map(len,data.values()))==summary['expanded_bytes']and len(raw)==summary['archive_bytes']
 J=lambda n:json.loads(data[n]);paths=J('paths.json')
 def saved(path):assert path in paths,path;return data[paths[path]]
 attempts=[('generic/run1','generic','RMNormalizedBisim','PASS',0,0,10),('generic/final/run2','generic/final','RMNormalizedBisim','PASS',0,0,10),('seed/run1','seed','KSeedModel222','PASS',0,9,4),('seed/final/run2','seed/final','KSeedModel222','FAIL',1,0,4),('seed/successor/run3','seed/successor','KSeedModel222','PASS',0,0,4)]
 results=[]
 for folder,base,module,status,code,warns,nreports in attempts:
  r=J(folder+'/result.json');log=data[folder+'/compiler.log'];source=data[base+'/'+module+'.lean'];audit=data[base+'/Audit.lean']
  assert r['status']==status and r['exit_code']==code and r['timed_out']is False
  assert r['basis_unchanged']and r['inputs_unchanged']and r['source_unchanged']
  assert sha(log)==r['log_sha256']and log.decode().count('warning:')==warns==r['warnings']
  assert sha(source)==r['candidate_sha256']and sha(audit)==r['audit_sha256']
  assert saved(r['source'])==source+audit and sha(source+audit)==r['source_sha256']
  assert r['timeout_seconds']==120 and r['memory_mebibytes']==12288 and r['command'][1:3]==['-j1','-M12288']
  assert sha(data[base+'/run.py'])==r['runner_sha256']
  src=PurePosixPath(r['source']);runroot=src.parents[3]
  expected=[r['command'][0],'-j1','-M12288','--root='+str(src.parents[2]),'-o',str(runroot/'objects'/'BusyBeaver'/'ZFC'/(module+'.olean')),str(src)]
  assert r['command']==expected
  assert r['compiler_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
  assert r['helper_sha256']=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
  assert len(r['basis_objects'])==184
  reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log.decode());assert [list(x)for x in reports]==r['axiom_reports']and len(reports)==nreports
  assert all({z.strip()for z in ax.split(',')if z.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports)
  if status=='PASS':assert 'error:'not in log.decode()and r['object_sha256']
  else:assert 'error:'in log.decode()
  results.append({'record':folder+'/result.json','status':status,'seconds':r['seconds'],'warnings':warns,'reports':nreports})
 c=J('normalized/comparison.json');assert c['status']=='PASS_STRUCTURAL_FINITE_ONLY'and(c['old_entries'],c['normalized_entries'],c['merged_entries'])==(2240,1426,814)
 assert c['both_successors_class_consistent']and c['root_index']==0 and c['exact_supplied_entries_match']
 assert c['local_obligations']=={'decrement_entries':1425,'halt_entries':1,'branch_checks':2851,'consumed_paths_used_before_arithmetic':True}
 assert len(c['negative_controls'])==4 and all(x['rejected']for x in c['negative_controls'])
 assert c['primary_modules']==186 and c['unchanged_check_modules']==16 and c['endpoint_declarations_exact']
 assert c['compiler_executed']is False and c['canonical_mutation']is False
 for name in ['normalized/generation-run1/result.json','normalized/regeneration-run1/result.json','fast/run1/result.json','fast/prepare-control/result.json']:
  r=J(name);assert r['status']in ['PASS','PASS_PYTHON_REGENERATION_ONLY','PASS_SOURCE_PRODUCER_ONLY'];assert all(x['exit_code']==0 for x in r['jobs']);assert r['compiler_executed']is False
 fast=J('fast/run1/result.json');assert fast['primary_project_modules']==187 and fast['physical_leaf_count']==4751 and fast['blocks_105_statements_exact']and fast['facade_proof_exact']
 assert [b for row in fast['batches']for b in row['blocks']]==[f'block_{i}'for i in range(105)]
 a=J('adoption/adoption.json');m=J('fast/combined-adoption-map.json');assert len(a['files'])==21 and a['files'][:20]==m['rows']
 assert sha(data['fast/combined-adoption-map.json'])==a['source_map_sha256']
 for r in a['files']+m['regenerated_unchanged']:
  assert sha(saved(r['source']))==r['sha256']
 assert len(m['regenerated_unchanged'])==16
 ar=J('adoption/adoption-review.json');assert ar['status']=='PASS_SOURCE_ADOPTION_BINDINGS_ONLY'and ar['current_project_sources']==187
 assert sha(data['adoption/adoption.json'])==ar['adoption_sha256']==summary['adoption_sha256']
 assert sha(data['adoption/pre-run-inventory.json'])==ar['pre_run_inventory_sha256']
 gp=J('generic-peer/review.json');sp=J('seed-peer/review.json');assert sp['candidate_sha256']==a['files'][-1]['sha256']
 for name,h in gp['files'].items():assert sha(data['generic/final/'+name])==h
 for module,row in gp['actual_correspondence']['imported_project_closure_checked'].items():
  assert sha(data['provider-sources/'+module.split('.')[-1]+'.lean'])==row['source_sha256']
 assert sp['result_sha256']==sha(data['seed/successor/run3/result.json'])
 assert sp['log_sha256']==sha(data['seed/successor/run3/compiler.log'])
 assert sp['diff_sha256']==sha(data['seed/successor/source.diff'])
 # All statement acceptance above concerns the saved isolated attempts/finite controls only.
 return {'status':'PASS_SAVED_FEATURE_EVIDENCE','archive_sha256':summary['archive_sha256'],'members':len(data),'no_compiled_objects':True,'isolated_attempts':results,'adopted_source_files_bound':21,'generic_peer_preserved_sha256':sha(data['generic-peer/review.json']),'seed_peer_preserved_sha256':sha(data['seed-peer/review.json']),'combined_phase6_status':'not assessed; separate root-owned full closure required','scope':'Saved-byte/source/log/finite-control bindings only; no live object/provider/toolchain audit or proof execution.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('directory',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();r=review(a.directory);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
