"""Own raw-run inspection; never executes proof or delivery code."""
from pathlib import Path
import argparse,hashlib,json,re
S=Path('/tmp/k215-phase15-check')
B=Path('/tmp/k215-phase14-check')
O=Path('/tmp/k215-phase15-root')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
pattern=re.compile(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)")
def reports(path):
    text=Path(path).read_text()
    assert 'error:' not in text and 'sorryAx' not in text
    return [(n,{s.strip() for s in a.split(',') if s.strip()}) for n,a in pattern.findall(text)]
def check_run(directory,map_path,count,expected_origins):
    result=read(directory/'result.json');inv=read(directory/'inventory.json');done=read(directory/'completed.json')
    before=read(directory/'before.json')
    assert result['status']=='PASS' and len(done)==len(inv['modules'])==count
    assert sha(directory/'inventory.json')==result['inventory_sha256']
    assert sha(directory/'completed.json')==result['completed_sha256']
    assert sha(S/'build.py')==result['runner_sha256'] and sha(map_path)==result['map_sha256']
    assert sha(S/'producer-boundary.json')==result['producer_boundary_sha256']
    for path,digest in before['inputs'].items():assert sha(path)==digest,path
    for path in before['absent_inputs']:assert not Path(path).exists() and not Path(path).is_symlink(),path
    specs={r['module']:r for r in read(map_path)['modules']}
    origins={};warning_rows=[];client_profiles={}
    for entry in inv['modules']:
        name=entry['module'];rec=done[name]
        assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
        assert sha(entry['source'])==entry['source_sha256']==rec['source_sha256']
        assert sha(directory/'objects'/(name.replace('.','/')+'.olean'))==rec['object_sha256']
        assert sha(rec['log'])==rec['log_sha256']
        assert rec['dependencies']=={d:done[d]['object_sha256'] for d in entry['imports'] if d!='Init'}
        origins[rec['origin']]=origins.get(rec['origin'],0)+1
        raw=reports(rec['log']);assert all(ax<={'propext','Classical.choice','Quot.sound'} for _,ax in raw)
        spec=specs.get(name,{})
        if 'reports' in spec:
            assert [n for n,_ in raw]==spec['reports']
            if 'report_axioms' in spec:assert [ax for _,ax in raw]==[set(ax) for ax in spec['report_axioms']]
            assert 'warning:' not in Path(rec['log']).read_text()
            client_profiles[name]=[[n,sorted(ax)] for n,ax in raw]
        if 'warning:' in Path(rec['log']).read_text():
            warning_rows.append({'module':name,'origin':rec['origin'],'count':Path(rec['log']).read_text().count('warning:')})
        if rec['origin']=='candidate_fresh':
            assert sha(rec['source'])==rec['source_sha256']
            assert rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
            assert rec['command'][1:3]==['-j1','-M12288']
            assert sha(rec['command'][0])==rec['compiler_sha256']
    assert origins==expected_origins,(origins,expected_origins)
    old_audits={r['module']:r for r in read(B/'primary-run2/result.json')['audits']}
    for audit in result['audits']:
        assert audit['status']=='PASS' and audit['exit_code']==0 and not audit['timed_out']
        for key in ['log','source']:assert sha(audit[key])==audit[key+'_sha256']
        assert sha(directory/('audit-'+audit['module'])/(audit['module']+'.olean'))==audit['object_sha256']
        assert [list(r) for r in pattern.findall(Path(audit['log']).read_text())]==audit['named_reports']
        assert audit['named_reports']==old_audits[audit['module']]['named_reports']
        assert 'warning:' not in Path(audit['log']).read_text()
    return {'directory':str(directory),'result_sha256':sha(directory/'result.json'),'providers':count,
        'origins':origins,'before_inputs_rehashed':len(before['inputs']),'warnings':warning_rows,
        'audits':len(result['audits']),'client_profiles':client_profiles},inv,done
ap=argparse.ArgumentParser();ap.add_argument('--primary',type=Path,required=True);ap.add_argument('--primary-map',type=Path,required=True)
ap.add_argument('--compatibility-map',type=Path,required=True);a=ap.parse_args()
p,pi,pd=check_run(a.primary,a.primary_map,194,{'candidate_fresh':45,'phase14_primary_checked':149})
c,ci,cd=check_run(S/'compatibility-run1',a.compatibility_map,71,{'candidate_fresh':6,'secondary_checked':54,'phase14_compatibility_checked':11})
sites=[m for m in pd if 'KSites215Batch' in m];assert len(sites)==9
old=read(B/'primary-run2/completed.json')
for m in sites:
    for key in ['source_sha256','object_sha256','dependencies','log_sha256']:assert pd[m][key]==old[m][key]
project={r['module']:r for r in pi['modules']+ci['modules'] if '.' in r['module']};assert len(project)==199
assert 'BusyBeaver.ZFC.PowerSets' in project and 'BusyBeaver.ZFC.KProfileTC' not in project
for m in set(pd)&set(cd):assert pd[m]['object_sha256']==cd[m]['object_sha256']
record={'status':'PASS_ROOT_RAW_PHASE15_ACTUAL','primary':p,'compatibility':c,'distinct_project_modules':199,
    'exact_inherited_site_batches':sites,'sources':{m:{'path':r['source'],'sha256':r['source_sha256']} for m,r in project.items()},
    'scope':'Raw actual inventories, sources, objects, logs, dependencies, commands, reports and before-input hashing. No compiler, producer, saved replay or adoption.'}
(O/'root-actual-review.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS raw phase15:194primary,71compatibility,199projectsources')
