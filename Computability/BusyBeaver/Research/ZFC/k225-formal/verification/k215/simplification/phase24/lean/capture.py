#!/usr/bin/env python3
'''Unexecuted phase24 deterministic capture template; root must review final schema.

Accepts only pinned, explicitly named inert files. Does not run proof tools,
generators or captured helpers. The phase23 leaf is an exact external boundary.
'''
from pathlib import Path, PurePosixPath
from io import BytesIO
import argparse, gzip, hashlib, json, re, tarfile

R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PREVIOUS=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase23/lean'
CORE={'README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py',
      'evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py'}
FORBIDDEN={'.olean','.ilean','.o','.obj','.a','.so','.dylib','.dll','.exe'}
sha=lambda data:hashlib.sha256(data).hexdigest()
dump=lambda x:(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def pin(row):
    p=Path(row['source']);h=row['sha256']
    assert p.is_absolute() and '..' not in p.parts and p.is_file() and not p.is_symlink(),str(p)
    assert re.fullmatch('[0-9a-f]{64}',h),h
    b=p.read_bytes();assert sha(b)==h,str(p)
    return b

def safe(name):
    p=PurePosixPath(name)
    assert name and '\\' not in name and '\x00' not in name and not p.is_absolute()
    assert '..' not in p.parts and str(p)==name and p.suffix not in FORBIDDEN and 'objects' not in p.parts
    return name

def main():
    a=argparse.ArgumentParser();a.add_argument('--config',type=Path,required=True);a.add_argument('--out',type=Path,required=True)
    args=a.parse_args();config_bytes=args.config.read_bytes();cfg=json.loads(config_bytes)
    assert cfg['status']=='FROZEN_FOR_CAPTURE_AFTER_ACTUAL_PASS'
    helper=Path(__file__).resolve();assert sha(helper.read_bytes())==cfg['capture_helper_sha256']
    out=args.out.absolute();assert not out.exists() and not out.is_symlink()
    review=json.loads(pin(cfg['actual_review']));raw=json.loads(pin(cfg['raw_copy_plan']))
    assert review['status']=='PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK'
    expected=cfg['expected_counts']
    assert all(review[k]==expected[k] for k in ['providers','projects','typed_clients','fresh','reuses','audits'])
    assert (review['client_reports'],review['WFTheory_reports'],review['audit_reports'])==(93,5,10)
    assert review['exact_profiles_preserved'] and review['all_source_object_dependency_log_toolchain_bindings_checked']
    assert review['fresh_provider_warnings']==review['fresh_client_audit_warnings']==0
    assert review['auditor']['path']==cfg['actual_review_helper']['source'] and review['auditor']['sha256']==cfg['actual_review_helper']['sha256']
    assert raw['status']=='DRAFT_COPY_PLAN_NO_MUTATION'
    boundaries={r['source']:r for r in cfg['external_boundaries']}
    assert len(boundaries)==11 and set(boundaries)=={str(PREVIOUS/n) for n in CORE}
    required={};results={};plans={};historical={}
    assert set(cfg['runs'])=={'candidate'}
    for name,counts in [('candidate',(expected['fresh'],expected['reuses'],expected['audits']))]:
        run=cfg['runs'][name]
        assert set(run)=={'workspace','plan','runner','result','inventory','completed','before','toolchain','stdout','stderr','outer','freeze','launcher'}
        content={k:pin(v) for k,v in run.items() if k!='workspace'}
        for k,v in run.items():
            if k!='workspace':required[v['source']]=v['sha256']
        plan=json.loads(content['plan']);result=json.loads(content['result']);done=json.loads(content['completed'])
        before=json.loads(content['before']);outer=json.loads(content['outer'])
        assert result['status']=='PASS' and result['provider_count']==len(plan['modules'])==len(done)==expected['providers']
        assert (len(result['fresh_modules']),len(result['reused_modules']),len(result['audits']))==counts
        assert result['source_transitive_reuse_only'] and result['all_source_object_dependency_log_toolchain_inputs_postchecked']
        assert result['map_sha256']==before['plan_sha256']==run['plan']['sha256']
        assert result['runner_sha256']==before['runner_sha256']==run['runner']['sha256']
        assert result['inventory_sha256']==run['inventory']['sha256'] and result['completed_sha256']==run['completed']['sha256']
        # The launcher receipt's terminal status/key names must match the reviewed root launcher.
        assert outer['status']=='PASS_EXIT_ZERO' and outer['exit_code']==0
        assert outer['stdout_sha256']==run['stdout']['sha256'] and outer['stderr_sha256']==run['stderr']['sha256']
        assert outer['freeze_sha256']==run['freeze']['sha256'] and outer['launcher_sha256']==run['launcher']['sha256']
        workspace=Path(run['workspace']);assert workspace.is_absolute()
        for row in plan['modules']:
            p=workspace/Path(*row['module'].split('.')).with_suffix('.lean')
            required[str(p)]=row['source_sha256'];historical[str(p)]=row['source']
        for module in result['fresh_modules']:
            row=done[module];assert row['status']=='PASS' and row['exit_code']==0 and not row['timed_out']
            assert row['warnings']==0
            log=Path(row['log']);required[str(log)]=row['log_sha256']
            record=log.parent/'record.json';required[str(record)]=sha(record.read_bytes())
            source=log.parent/(module.split('.')[-1]+'.lean');required[str(source)]=row['source_sha256']
        for row in result['audits']:
            assert row['status']=='PASS' and row['exit_code']==0 and not row['timed_out'] and row['warnings']==0
            required[row['source']]=row['source_sha256'];required[row['log']]=row['log_sha256']
            record=Path(row['log']).parent/'record.json';required[str(record)]=sha(record.read_bytes())
        results[name]=result;plans[name]=plan
    assert results['candidate']['basis_result_sha256']==boundaries[str(PREVIOUS/'result.json')]['sha256']
    assert review['result']['path']==cfg['runs']['candidate']['result']['source'] and review['result']['sha256']==cfg['runs']['candidate']['result']['sha256']
    assert review['basis_result']['sha256']==boundaries[str(PREVIOUS/'result.json')]['sha256']
    for context in cfg.get('failed_contexts',[]):
        outer=json.loads(pin(context['outer']))
        assert context['accepted_as_current_result'] is False
        assert outer['status']==context['terminal_status'] and outer['status']!='PASS_EXIT_ZERO'
        assert outer['exit_code']!=0
        required[context['outer']['source']]=context['outer']['sha256']
        for row in context['files']:required[row['source']]=row['sha256']
    rows=raw['files'];covered={r['source']:r['sha256'] for r in rows}
    assert all(covered.get(p)==h for p,h in required.items()),'Raw copy plan omits required accepted evidence'
    logical={};sources={};blobs={};bindings={};external={}
    def bind(row,name,role,is_external=False):
        name=safe(name);assert name not in logical,name
        p=Path(row['source']);assert not p.is_relative_to(out)
        assert p.suffix not in FORBIDDEN and 'objects' not in p.parts
        if is_external:assert str(p) in boundaries
        else:
            assert not p.is_relative_to(PREVIOUS),'Keep the previous packet external'
            assert not str(p).endswith(('.tar','.tar.gz','.tgz','.zip'))
        b=pin(row);h=sha(b);bindings[str(p)]=h
        item={'source':str(p),'sha256':h,'bytes':len(b),'role':role}
        if 'historical_source' in row:item['historical_source']=row['historical_source']
        if is_external:item['external']=True;external[str(p)]=h
        else:item['blob']='blobs/'+h;blobs[h]=b
        logical[name]=item
        alias=sources.setdefault(str(p),{'sha256':h,'bytes':len(b),'external':is_external,'logical':[]})
        assert (alias['sha256'],alias['bytes'],alias['external'])==(h,len(b),is_external)
        alias['logical'].append(name)
    for row in rows:
        row=dict(row)
        if row['source'] in historical:row['historical_source']=historical[row['source']]
        bind(row,'runtime/'+safe(row['destination']),row.get('role','accepted_candidate_raw'))
        assert logical['runtime/'+row['destination']]['bytes']==row['bytes']
    for row in cfg['external_boundaries']:bind(row,row['logical'],'exact_phase23_leaf_boundary',True)
    for row in cfg['files']:bind(row,row['logical'],row['role'])
    for key,name in [('actual_review','capture/actual-review.json'),('actual_review_helper','capture/review_actual.py'),('raw_copy_plan','capture/raw-copy-plan.json')]:
        bind(cfg[key],name,key)
    bind({'source':str(helper),'sha256':cfg['capture_helper_sha256']},'capture/capture.py','owned_capture_helper')
    bind({'source':str(args.config.absolute()),'sha256':sha(config_bytes)},'capture/config.json','owned_capture_config')
    candidate_plan=json.loads(pin(cfg['runs']['candidate']['plan']))
    for p,h in candidate_plan['present_inputs'].items():
        assert sha(Path(p).read_bytes())==h and bindings.get(p)==h
    assert len(candidate_plan['absent_inputs'])==expected['absences']
    for p in candidate_plan['absent_inputs']:assert not Path(p).exists() and not Path(p).is_symlink()
    out.mkdir(parents=True,exist_ok=False);archive=out/'evidence.tar.gz'
    with archive.open('xb') as stream:
        with gzip.GzipFile(filename='',fileobj=stream,mode='wb',mtime=0) as zipped:
            with tarfile.open(fileobj=zipped,mode='w',format=tarfile.USTAR_FORMAT) as tar:
                for h,b in sorted(blobs.items()):
                    m=tarfile.TarInfo('blobs/'+h);m.size=len(b);m.mode=0o644;m.uid=m.gid=m.mtime=0;m.uname=m.gname=''
                    tar.addfile(m,BytesIO(b))
    # Inspect only the archive just created; never extract members to the filesystem.
    with tarfile.open(archive,'r:gz') as tar:
        members=tar.getmembers();assert len(members)==len(blobs) and len({m.name for m in members})==len(members)
        assert {m.name for m in members}=={'blobs/'+h for h in blobs}
        for m in members:
            assert m.isfile() and not m.issym() and not m.islnk() and safe(m.name)==m.name
            assert m.uid==m.gid==m.mtime==0 and m.mode==0o644
            b=tar.extractfile(m).read();assert b==blobs[m.name[6:]] and sha(b)==m.name[6:] and len(b)==m.size
    for p,h in bindings.items():assert sha(Path(p).read_bytes())==h
    for p in candidate_plan['absent_inputs']:assert not Path(p).exists() and not Path(p).is_symlink()
    for row in sources.values():row['logical'].sort()
    index={'format':'phase24-explicit-evidence-blobs-v1','archive_sha256':sha(archive.read_bytes()),'logical':dict(sorted(logical.items())),'sources':dict(sorted(sources.items())),'external_boundaries':external,'scope':'Inert source/raw evidence; exact prior packet external; historical paths are labels and verified snapshot paths are actual byte providers.'}
    (out/'index.json').write_bytes(dump(index))
    receipt={'status':'PASS_DETERMINISTIC_CAPTURE_AND_MEMBER_HASH_VERIFICATION','archive_sha256':index['archive_sha256'],'archive_bytes':archive.stat().st_size,'index_sha256':sha((out/'index.json').read_bytes()),'blob_members':len(blobs),'logical_entries':len(logical),'source_aliases':len(sources),'external_boundary_files':len(external),'raw_plan_files':len(rows),'capture_helper_sha256':cfg['capture_helper_sha256'],'config_sha256':sha(config_bytes),'actual_review_sha256':cfg['actual_review']['sha256'],'compiler_execution':False,'supplied_code_execution':False,'objects_copied':False,'current_runs':1,'preserved_failed_contexts':len(cfg.get('failed_contexts',[]))}
    (out/'capture.json').write_bytes(dump(receipt));print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
