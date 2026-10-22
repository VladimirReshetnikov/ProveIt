"""Own raw-run receipt reader; hashes source/objects/logs without running proof code."""
from pathlib import Path
import hashlib,json,re
P=Path('/tmp/k215-phase13-upstream-check')
B=Path('/tmp/k215-phase12-import-check')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
report_re=re.compile(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)")
def reports(path):
 text=Path(path).read_text();assert 'error:' not in text and 'sorryAx' not in text
 return [[name,[a.strip() for a in axioms.split(',') if a.strip()]] for name,axioms in report_re.findall(text)]
def check_run(name,count,origins,mapname):
 directory=P/name;result=read(directory/'result.json');inventory=read(directory/'inventory.json');done=read(directory/'completed.json');before=read(directory/'before.json')
 assert result['status']=='PASS' and len(done)==len(inventory['modules'])==count
 assert sha(directory/'inventory.json')==result['inventory_sha256'] and sha(directory/'completed.json')==result['completed_sha256']
 assert sha(P/'build.py')==result['runner_sha256'] and sha(P/mapname)==result['map_sha256']
 assert sha(P/'producer-boundary.json')==result['producer_boundary_sha256']
 for path,digest in before['inputs'].items():assert sha(path)==digest,path
 for path in before['absent_inputs']:assert not Path(path).exists() and not Path(path).is_symlink(),path
 overrides={r['module']:r for r in read(P/mapname)['modules']};actual={};warnings={'fresh':0,'inherited':0}
 for entry in inventory['modules']:
  module=entry['module'];rec=done[module];assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
  assert sha(entry['source'])==entry['source_sha256']==rec['source_sha256']
  assert sha(directory/'objects'/(module.replace('.','/')+'.olean'))==rec['object_sha256']
  assert sha(rec['log'])==rec['log_sha256']
  assert rec['dependencies']=={d:done[d]['object_sha256'] for d in entry['imports'] if d!='Init'}
  actual[rec['origin']]=actual.get(rec['origin'],0)+1
  raw=reports(rec['log']);assert all(set(ax)<= {'propext','Classical.choice','Quot.sound'} for _,ax in raw)
  spec=overrides.get(module,{})
  if 'reports' in spec:
   assert [n for n,_ in raw]==spec['reports'];assert [set(ax) for _,ax in raw]==[set(ax) for ax in spec['report_axioms']]
   assert 'warning:' not in Path(rec['log']).read_text()
  warnings['fresh' if rec['origin']=='candidate_fresh' else 'inherited']+=Path(rec['log']).read_text().count('warning:')
  if rec['origin']=='candidate_fresh':
   assert sha(rec['source'])==rec['source_sha256'];assert rec['timeout_seconds']==(900 if 'KSites215Batch' in module else 120)
   assert rec['memory_mebibytes']==12288;assert rec['command'][1:3]==['-j1','-M12288'];assert sha(rec['command'][0])==rec['compiler_sha256']
 assert actual==origins,(actual,origins)
 for audit in result['audits']:
  assert audit['status']=='PASS' and audit['exit_code']==0 and not audit['timed_out']
  assert sha(audit['log'])==audit['log_sha256'] and sha(audit['source'])==audit['source_sha256']
  assert sha(directory/('audit-'+audit['module'])/(audit['module']+'.olean'))==audit['object_sha256']
  assert [list(r) for r in report_re.findall(Path(audit['log']).read_text())]==audit['named_reports'];assert 'warning:' not in Path(audit['log']).read_text()
  baseline=next(r for r in read(B/'primary-run1/result.json')['audits'] if r['module']==audit['module'])
  assert audit['named_reports']==baseline['named_reports']
 return {'directory':str(directory),'result_sha256':sha(directory/'result.json'),'providers':count,'origins':actual,'before_inputs_rehashed':len(before['inputs']),'warnings':warnings,'audits':len(result['audits'])},inventory,done
primary,pi,pd=check_run('primary-run1',187,{'candidate_fresh':36,'phase12_primary_checked':151},'primary-map.json')
compat,ci,cd=check_run('compatibility-run1',70,{'candidate_fresh':16,'secondary_checked':53,'phase12_compatibility_checked':1},'compatibility-final-map.json')
baseline=read(B/'primary-run1/completed.json')
sites=[m for m in pd if 'KSites215Batch' in m];assert len(sites)==9
for m in sites:
 for key in ['source_sha256','object_sha256','dependencies','log_sha256']:assert pd[m][key]==baseline[m][key]
project={e['module']:e for e in pi['modules']+ci['modules'] if '.' in e['module']};assert len(project)==199
for module in set(pd)&set(cd):assert pd[module]['object_sha256']==cd[module]['object_sha256']
record={'status':'PASS_ROOT_RAW_PHASE13_ACTUAL','primary':primary,'compatibility':compat,'distinct_project_modules':199,'exact_inherited_site_batches':sites,'sources':{m:{'path':r['source'],'sha256':r['source_sha256']} for m,r in project.items()},'scope':'Raw actual inventory/source/object/log/dependency/command/report and before-input hashing only. No compiler, producer, saved-packet replay or canonical adoption.'}
Path('/tmp/k215-phase13-root/root-actual-review.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS raw phase13:187 primary,70 compatibility,199 project sources')
