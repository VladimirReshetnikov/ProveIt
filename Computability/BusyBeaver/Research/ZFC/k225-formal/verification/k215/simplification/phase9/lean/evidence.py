"""Validate saved phase9 bytes; no proof compiler or archived Python is executed."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import basis_reference

HERE = Path(__file__).resolve().parent
TARGETS = ['BusyBeaver.ZFC.KEndpoint215', 'BusyBeaver.ZFC.KDecoderPrefix215']
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SUFFIXES = {'.olean', '.ilean', '.o', '.so', '.a', '.vo', '.vos', '.vok', '.glob', '.pyc', '.pyo'}
AUDIT_PINS = {
    'EndpointAudit215': 'd13596021774c5b26937b13cf6cca58342af99f59626b9205ff10b9df1e6fc7d',
    'K215Audit': '9144acc6c597c4a53928fc62be00d5e25d9f32f519797d17a5058d03b5460986',
}
REPORTS = {
    'EndpointAudit215': ['EndpointAudit215.blank_halts_exactly_when_zfc_has_a_finite_refutation',
                         'EndpointAudit215.nonhalting_exactly_when_zfc_is_consistent'],
    'K215Audit': ['SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation',
                 'SetTheory.BusyBeaver.ZFC.KEndpoint215.nonhalting_iff_zfc_consistency',
                 'SetTheory.BusyBeaver.ZFC.KDense215.commutes', 'SetTheory.BusyBeaver.ZFC.KBoot215.boot',
                 'SetTheory.BusyBeaver.ZFC.KSites215.covered', 'SetTheory.BusyBeaver.ZFC.KEndpoint215.p215_boot_iff',
                 'K215Audit.blank_halts_exact', 'K215Audit.nonhalting_exact'],
}
ROOTS = ('Computability/BusyBeaver/Lean', 'Logic/FirstOrder/Lean',
         'SetTheory/ZF/Lean', 'SetTheory/BoundedConsistency/Lean')


def digest(data): return hashlib.sha256(data).hexdigest()
def sha(path): return digest(Path(path).read_bytes())
def binary_name(path): return bool(set(PurePosixPath(path).suffixes) & SUFFIXES)
def dump(value): return (json.dumps(value, indent=2) + '\n').encode()
def save(path, value):
    with Path(path).open('xb') as stream: stream.write(dump(value))
def manifest(members):
    return {n: {'sha256': digest(b), 'bytes': len(b)} for n,b in sorted(members.items())}
def manifest_hash(members):
    return digest(json.dumps(manifest(members), sort_keys=True, separators=(',', ':')).encode())
def safe_name(name):
    path=PurePosixPath(name)
    assert not path.is_absolute() and '..' not in path.parts and str(path)==name
    assert not binary_name(name) and path.suffix not in {'.gz','.zip','.tar'}, name

def imports(data):
    text=data.decode();out=[];i=depth=0
    while i<len(text):
        pair=text[i:i+2]
        if pair=='/-': depth+=1;i+=2
        elif depth and pair=='-/': depth-=1;i+=2
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        elif pair=='--':
            end=text.find('\n',i);i=len(text) if end<0 else end
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
        else:out.append(text[i]);i+=1
    assert depth==0
    return [w for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)', ''.join(out)) for w in line.split()]

def reports(data):
    text=data.decode()
    assert 'error:' not in text and 'sorryAx' not in text and "declaration uses 'sorry'" not in text
    rows=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)
    assert all({x.strip() for x in ax.split(',') if x.strip()}<=AXIOMS for _,ax in rows)
    return rows

def graph(rows, targets):
    entries={r['module']:r for r in rows};assert len(entries)==len(rows)
    seen=set();closures={}
    for r in rows:
        assert set(r['imports'])<=seen|{'Init'}
        closures[r['module']]={r['module']}|set().union(*(closures[d] for d in r['imports'] if d!='Init'))
        seen.add(r['module'])
    assert set().union(*(closures[t] for t in targets))==seen
    return entries,closures

def source_scope(entries, closures, old_entries, iso_entries):
    changed={m for m,e in entries.items() if m not in old_entries or
             (e['source_sha256'],e['imports'])!=(old_entries[m]['source_sha256'],old_entries[m]['imports'])}
    forced={m for m in entries if closures[m]&changed}
    iso_ok={m for m in entries if closures[m]<=set(iso_entries) and all(
        (entries[d]['source_sha256'],entries[d]['imports'])==(iso_entries[d]['source_sha256'],iso_entries[d]['imports'])
        for d in closures[m])}
    return changed,forced,iso_ok


def check_origins(done, forced, iso_ok):
    for m,rec in done.items():
        assert rec['origin'] in {'phase9_fresh','phase8_checked','isolated_checked'}
        if rec['origin']=='phase8_checked':assert m not in forced
        if rec['origin']=='isolated_checked':assert m in iso_ok
    assert all(done[m]['origin']=='phase9_fresh'for m in forced-iso_ok)


def validate(members, basis_repo, repo=None):
    for name in members:safe_name(name)
    read=lambda n:json.loads(members[n])
    assert members['review/basis-reference.json']==(HERE/'basis-reference.json').read_bytes()
    prior,_,_=basis_reference.validate(basis_repo,members['review/basis-reference.json'])
    pathmap=read('path-map.json');resolved={}
    for path,route in pathmap.items():
        assert PurePosixPath(path).is_absolute() and not binary_name(path)
        assert set(route)=={'storage','member','sha256','bytes'}
        source=members if route['storage']=='packet' else prior
        assert route['storage'] in {'packet','phase8'}
        data=source[route['member']]
        assert digest(data)==route['sha256'] and len(data)==route['bytes']
        resolved[path]=data
    def at(path):return resolved[str(path)]
    def at_json(path):return json.loads(at(path))
    configuration=read('review/config.json');run=PurePosixPath(configuration['run'])
    result=read('execution/result.json');before=read('execution/before.json')
    inv=read('execution/inventory.json');done=read('execution/completed.json')
    plan=read('execution/map.json');toolchain=read('execution/toolchain.json')
    assert result['status']=='PASS' and result['targets']==inv['targets']==before['targets']==TARGETS
    assert result['selected_project_modules']==197 and inv['external_imports']==before['external_imports']==['Init']
    assert before['rows']==inv['modules'] and before['audit_endpoint'] is True
    for name,key in [('inventory.json','inventory_sha256'),('completed.json','completed_sha256')]:
        assert digest(members['execution/'+name])==result[key]
    assert result['runner_sha256']==before['runner_sha256']==configuration['driver_sha256']==digest(members['execution/build.py'])
    assert result['map_sha256']==before['map_sha256']==configuration['map_sha256']==digest(members['execution/map.json'])
    assert result['inputs_sources_objects_dependencies_logs_toolchain_rechecked']
    assert result['basis_reuse_rejects_transitive_source_changes']
    assert result['isolated_reuse_requires_exact_transitive_sources_and_imports']
    prior_inv=json.loads(prior['execution/inventory.json']);old=json.loads(prior['execution/completed.json'])
    old_entries={r['module']:r for r in prior_inv['modules']};assert len(old_entries)==len(old)==188
    assert digest(prior['execution/result.json'])==configuration['basis_result_sha256']
    assert members['execution/toolchain.json']==prior['execution/toolchain.json']
    entries,closures=graph(inv['modules'],TARGETS)
    assert len(entries)==len(done)==197 and set(entries)==set(done)
    assert len(closures[TARGETS[0]])==192 and len(set(entries)-closures[TARGETS[0]])==5
    overrides={r['module']:r for r in plan['modules']};assert len(overrides)==len(plan['modules'])==11
    assert len(set(entries)-set(old_entries))==9 and set(old_entries)<set(entries)
    for m,e in entries.items():
        if m in overrides:
            p=overrides[m]
            assert all(e[k]==p[k] for k in ('source','source_sha256','imports'))
            assert p['before_sha256']==(old_entries[m]['source_sha256'] if m in old_entries else None)
        else:assert e==old_entries[m]
    iso_dir=PurePosixPath(plan['reuse_ledger']['directory'])
    for name in ('result.json','inventory.json','completed.json'):
        assert digest(at(iso_dir/name))==plan['reuse_ledger'][name]
    iso_result=at_json(iso_dir/'result.json');iso=at_json(iso_dir/'completed.json')
    iso_entries={r['module']:r for r in at_json(iso_dir/'inventory.json')['modules']}
    assert iso_result['status']=='PASS' and len(iso)==len(iso_entries)==14
    changed,forced,iso_ok=source_scope(entries,closures,old_entries,iso_entries)
    assert changed==set(overrides)
    assert sorted(changed)==before['changed_sources']==result['source_changed_modules']
    assert sorted(forced)==before['force_basis_rebuild']==result['force_basis_rebuild_modules']
    check_origins(done,forced,iso_ok)
    required=forced-iso_ok
    sites={m for m in entries if m.startswith('BusyBeaver.ZFC.KSites215Batch')};assert len(sites)==9
    assert sites<=required
    fresh=set(result['fresh_modules']);reused=set(result['phase8_reused_modules']);isolated=set(result['isolated_reused_modules'])
    assert len(fresh)==len(result['fresh_modules']) and len(reused)==len(result['phase8_reused_modules']) and len(isolated)==len(result['isolated_reused_modules'])
    assert not(fresh&reused or fresh&isolated or reused&isolated) and fresh|reused|isolated==set(entries)
    assert required<=fresh and not(reused&forced) and isolated<=iso_ok
    # Every saved nonbinary input binding is checked, not merely collected.
    # Object/executable hashes are historical fingerprints, not archived objects.
    basis_dir=PurePosixPath(configuration['basis_run'])
    for path,pin in before['inputs'].items():
        if path in {toolchain[k]['path']for k in ('lean','lake','Init.olean')}:
            key=next(k for k in ('lean','lake','Init.olean')if toolchain[k]['path']==path)
            assert pin==toolchain[key]['sha256']
        elif binary_name(path):
            p=PurePosixPath(path)
            assert p.suffix=='.olean'
            if p.is_relative_to(basis_dir/'objects'):
                m=str(p.relative_to(basis_dir/'objects'))[:-6].replace('/','.')
                assert pin==old[m]['object_sha256']
            else:
                m=str(p.relative_to(iso_dir/'objects'))[:-6].replace('/','.')
                assert pin==iso[m]['object_sha256']
        else:assert digest(at(path))==pin,path
    for name in ('result.json','inventory.json','completed.json','toolchain.json'):
        assert at(basis_dir/name)==prior['execution/'+name]
    assert at(configuration['driver'])==members['execution/build.py']
    assert at(configuration['map'])==members['execution/map.json']
    assert digest(at(configuration['supervisor']))==configuration['supervisor_sha256']
    source_reports=warnings=0
    compiler=toolchain['lean']['path'];helper_sha=configuration['supervisor_sha256']
    for m,e in entries.items():
        rec=done[m];data=members['execution/sources/'+m.replace('.','/')+'.lean']
        assert data==at(e['source'])==at(run/'workspace'/(m.replace('.','/')+'.lean'))
        assert digest(data)==e['source_sha256']==rec['source_sha256'] and imports(data)==e['imports']
        assert rec['dependencies']=={d:done[d]['object_sha256'] for d in e['imports'] if d!='Init'}
        assert re.fullmatch('[0-9a-f]{64}',rec['object_sha256']) and rec['status']=='PASS'
        log=at(rec['log']);assert digest(log)==rec['log_sha256'];found=reports(log)
        warnings+=log.decode().count('warning:')
        if m in overrides:
            assert [n for n,_ in found]==overrides[m]['reports'] and 'warning:'not in log.decode()
            source_reports+=len(found)
        if m in reused:
            assert rec=={**old[m],'origin':'phase8_checked'}
            assert log==prior['execution/logs/'+m+'.log']
            assert pathmap[rec['log']]['storage']=='phase8'
        elif m in isolated:
            assert rec=={**iso[m],'origin':'isolated_checked'}
            without_origin=lambda r:{k:v for k,v in r.items()if k!='origin'}
            if m in old and without_origin(rec)==without_origin(old[m]):
                assert log==prior['execution/logs/'+m+'.log']
                assert pathmap[rec['log']]['storage']=='phase8'
            else:
                raw=read('isolated/provider-records/'+m+'.json')
                if 'dependencies' not in raw:
                    # The first bridge runner recorded its provider set separately.
                    # Its later isolated ledger adds exactly this reconstructed field.
                    assert m in {'BusyBeaver.ZFC.FramedWindow','BusyBeaver.ZFC.KZipTape'}
                    bridge_run=PurePosixPath(rec['log']).parent
                    assert str(bridge_run)=='/tmp/k215-phase9-zipbridge/run5'
                    bridge_before=at_json(bridge_run/'before.json');bridge_summary=at_json(bridge_run/'summary.json')
                    assert bridge_summary['status']=='PASS' and bridge_summary['inputs_unchanged']
                    assert bridge_summary['all_188_basis_objects_unchanged']
                    assert bridge_before['basis_objects']=={d:r['object_sha256']for d,r in old.items()}
                    bridge_rows=bridge_summary['rows']
                    assert [r['module']for r in bridge_rows]==['BusyBeaver.ZFC.FramedWindow','BusyBeaver.ZFC.KZipTape']
                    position=next(j for j,r in enumerate(bridge_rows)if r['module']==m)
                    assert bridge_rows[position]==raw
                    providers={**bridge_before['basis_objects'],**{r['module']:r['object_sha256']for r in bridge_rows[:position]}}
                    dependencies={d:providers[d]for d in e['imports']if d!='Init'}
                    assert rec['dependencies']==dependencies
                    assert bridge_before['inputs'][raw['candidate']]==raw['source_sha256']
                    runner=bridge_run.parent/'run.py'
                    assert digest(at(runner))==bridge_summary['runner_sha256']==bridge_before['inputs'][str(runner)]
                    assert without_origin({**raw,'dependencies':dependencies})==without_origin(rec)
                else:
                    assert without_origin(raw)==without_origin(rec)
                assert at(rec['source'])==data
                assert rec['exit_code']==0 and not rec['timed_out']
                assert rec['compiler_sha256']==toolchain['lean']['sha256'] and rec['helper_sha256']==helper_sha
                assert rec['memory_mebibytes']==12288 and rec['timeout_seconds']==120
                logpath=PurePosixPath(rec['log'])
                origin_run=logpath.parent.parent.parent if logpath.name=='compiler.log' else logpath.parent
                assert rec['source']==str(origin_run/'workspace'/(m.replace('.','/')+'.lean'))
                assert rec['command']==[compiler,'-j1','-M12288','--root='+str(origin_run/'workspace'),'-o',
                    str(origin_run/'objects'/(m.replace('.','/')+'.olean')),rec['source']]
                assert rec['warnings']==log.decode().count('warning:')==0
                assert [list(x)for x in found]==rec.get('reports',rec.get('axiom_reports'))
        else:
            assert rec['origin']=='phase9_fresh' and rec['exit_code']==0 and not rec['timed_out']
            assert rec['compiler_sha256']==toolchain['lean']['sha256'] and rec['helper_sha256']==helper_sha
            assert rec['memory_mebibytes']==12288 and rec['timeout_seconds']==(900 if m in sites else 120)
            assert rec['seconds']>=0 and rec['lock_wait_seconds']>=0
            assert rec['command']==[compiler,'-j1','-M12288','--root='+str(run/'workspace'),'-o',
                str(run/'objects'/(m.replace('.','/')+'.olean')),str(run/'workspace'/(m.replace('.','/')+'.lean'))]
            assert rec['source']==str(run/'workspace'/(m.replace('.','/')+'.lean'))
            assert rec['candidate']==e['source'] and rec['warnings']==log.decode().count('warning:')
            assert [list(x)for x in found]==rec['reports']
            attempt=PurePosixPath(rec['log']).parent
            assert attempt.parent==run/'attempts' and at_json(attempt/'record.json')==rec
            assert at(attempt/(m.rsplit('.',1)[-1]+'.lean'))==data
        if repo is not None:
            paths=[Path(repo)/root/(m.replace('.','/')+'.lean') for root in ROOTS]
            found_paths=[p for p in paths if p.is_file()]
            assert len(found_paths)==1 and sha(found_paths[0])==e['source_sha256'],m
    assert source_reports==27
    assert [r['module']for r in result['audits']]==list(REPORTS)
    for rec in result['audits']:
        name=rec['module'];folder=run/('audit-'+name)
        assert rec==at_json(folder/(name+'.json'))
        source=at(folder/(name+'.lean'));log=at(folder/(name+'.log'));found=reports(log)
        assert digest(source)==rec['source_sha256']==AUDIT_PINS[name]
        assert source==at(rec['source']) and digest(log)==rec['log_sha256'] and 'warning:'not in log.decode()
        assert [n for n,_ in found]==REPORTS[name] and [list(x)for x in found]==rec['named_reports']
        assert rec['status']=='PASS' and rec['exit_code']==0 and not rec['timed_out']
        assert rec['dependencies']=={m:r['object_sha256']for m,r in done.items()}
        assert rec['command']==[compiler,'-j1','-M12288','--root='+str(folder),'-o',str(folder/(name+'.olean')),str(folder/(name+'.lean'))]
        assert rec['compiler_sha256']==toolchain['lean']['sha256'] and rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
        assert re.fullmatch('[0-9a-f]{64}',rec['object_sha256'])
    # The immutable original first result remains present, but never supplies accepted records.
    qualification=read('history/full-run1-qualification.json')
    assert qualification['status']=='NOT_ACCEPTED_AS_NEW_ENDPOINT_CHECK' and not qualification['original_records_mutated']
    assert qualification['replacement_driver']=='build-v4.py' and qualification['replacement_run']=='full-run2'
    rejected=read('history/full-run1/completed.json')
    assert any(rejected[m]['origin']=='phase8_checked' for m in forced if m in rejected)
    context=read('review/context.json')
    for row in context['files']:
        assert digest(members[row['member']])==row['sha256'] and len(members[row['member']])==row['bytes']
        assert at(row['path'])==members[row['member']]
    assert {r['member']for r in context['files']}=={n for n in members if n.startswith('context/')}
    live=read('review/terminal-review.json')
    assert live['status']=='PASS_INDEPENDENT_197_TRANSITIVE_SOURCE_CLOSED_REVIEW'
    assert live['modules']==197 and live['exact_typed_clients']==2 and live['exact_named_reports']==10
    assert live['original_full_run1_rejected'] and live['audit_warnings']==0
    assert set(live['fresh_modules'])==required and set(live['all_nine_site_batches_fresh'])==sites
    assert live['pins'][configuration['terminal_reviewer']]==configuration['terminal_reviewer_sha256']
    for path,pin in live['pins'].items():assert digest(at(path))==pin
    for m,entry in live['ledger'].items():
        assert entry['source']==entries[m]['source_sha256'] and entry['object']==done[m]['object_sha256']
        assert entry['log']==done[m]['log_sha256'] and entry['origin']==done[m]['origin']
        assert entry['transitive_source_imports']=={d:{'source':entries[d]['source_sha256'],'imports':entries[d]['imports']}for d in sorted(closures[m])}
    assert set(live['ledger'])==set(entries)
    from auxiliary import validate_auxiliary
    auxiliary=validate_auxiliary(configuration,at,old,iso,toolchain,old_entries,iso_entries)
    return {'status':'PASS_SAVED_PHASE9_RECORDS','auxiliary':auxiliary,'union_modules':197,'endpoint_modules':192,
        'prefix_only_modules':sorted(set(entries)-closures[TARGETS[0]]),'changed_sources':len(changed),
        'affected_source_descendants':len(forced),'fresh_modules':len(fresh),'phase8_reused_modules':len(reused),
        'isolated_reused_modules':len(isolated),'all_nine_site_batches_fresh':sorted(sites),
        'component_reports':source_reports,'typed_clients':2,'typed_reports':10,'project_warnings':warnings,
        'audit_warnings':0,'raw_result_sha256':digest(members['execution/result.json']),
        'basis_result_sha256':configuration['basis_result_sha256'],'terminal_review_sha256':digest(members['review/terminal-review.json']),
        'compiled_objects_in_archive':False,'current_sources_checked':repo is not None,
        'scope':'Saved sources/imports/dependencies/object-hash records, raw commands/logs and exact local predecessor references. No compiler, archived-code execution, or live-object inspection by the saved reader.'}
