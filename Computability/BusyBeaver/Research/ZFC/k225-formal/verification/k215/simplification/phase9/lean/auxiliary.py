"""Check the separately completed readiness/old-executor/engine control run."""
from pathlib import PurePosixPath
import json
from evidence import binary_name, check_origins, digest, graph, imports, reports, source_scope

TARGETS=['BusyBeaver.ZFC.KHomeReadyControls','BusyBeaver.ZFC.KHomeRuntimeAudit',
         'BusyBeaver.ZFC.KEngine224','BusyBeaver.ZFC.KEngine225']
NAMES=['ready215','word_rows_still_pass','boundary_gate_rejects','fallback_stepper','fallback_executor']


def validate_auxiliary(configuration, at, old, iso, toolchain, old_entries, iso_entries):
    read=lambda p:json.loads(at(p))
    run=PurePosixPath(configuration['auxiliary_run'])
    result=read(run/'result.json');before=read(run/'before.json');inv=read(run/'inventory.json');done=read(run/'completed.json')
    plan=read(configuration['auxiliary_map']);overrides={r['module']:r for r in plan['modules']}
    assert digest(at(run/'result.json'))==configuration['auxiliary_result_sha256']
    assert digest(at(configuration['auxiliary_map']))==configuration['auxiliary_map_sha256']==result['map_sha256']==before['map_sha256']
    assert result['runner_sha256']==before['runner_sha256']==configuration['driver_sha256']
    assert result['status']=='PASS' and result['selected_project_modules']==18
    assert result['targets']==inv['targets']==before['targets']==TARGETS and before['rows']==inv['modules']
    assert result['audits']==[] and before['audit_endpoint'] is False
    assert result['inputs_sources_objects_dependencies_logs_toolchain_rechecked']
    assert result['basis_reuse_rejects_transitive_source_changes'] and result['isolated_reuse_requires_exact_transitive_sources_and_imports']
    assert digest(at(run/'inventory.json'))==result['inventory_sha256'] and digest(at(run/'completed.json'))==result['completed_sha256']
    assert read(run/'toolchain.json')==toolchain
    entries,closures=graph(inv['modules'],TARGETS)
    assert len(entries)==len(done)==18 and set(entries)==set(done)
    changed,forced,iso_ok=source_scope(entries,closures,old_entries,iso_entries)
    assert sorted(changed)==before['changed_sources']==result['source_changed_modules']
    assert sorted(forced)==before['force_basis_rebuild']==result['force_basis_rebuild_modules']
    check_origins(done,forced,iso_ok)
    origins={'phase9_fresh':[],'phase8_checked':[],'isolated_checked':[]};compiler=toolchain['lean']['path']
    for m,entry in entries.items():
        rec=done[m];src=at(run/'workspace'/(m.replace('.','/')+'.lean'));log=at(rec['log']);found=reports(log)
        assert digest(src)==entry['source_sha256']==rec['source_sha256'] and imports(src)==entry['imports']
        assert src==at(entry['source']) and digest(log)==rec['log_sha256'] and rec['status']=='PASS'
        assert rec['dependencies']=={d:done[d]['object_sha256']for d in entry['imports']if d!='Init'}
        origins[rec['origin']].append(m)
        if rec['origin']=='phase8_checked':assert rec=={**old[m],'origin':'phase8_checked'}
        elif rec['origin']=='isolated_checked':assert rec=={**iso[m],'origin':'isolated_checked'}
        else:
            assert rec['origin']=='phase9_fresh' and rec['exit_code']==0 and not rec['timed_out']
            assert rec['compiler_sha256']==toolchain['lean']['sha256'] and rec['helper_sha256']==configuration['supervisor_sha256']
            assert rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
            assert rec['source']==str(run/'workspace'/(m.replace('.','/')+'.lean'))
            assert rec['command']==[compiler,'-j1','-M12288','--root='+str(run/'workspace'),'-o',
                                   str(run/'objects'/(m.replace('.','/')+'.olean')),rec['source']]
            folder=PurePosixPath(rec['log']).parent
            assert folder.parent==run/'attempts' and read(folder/'record.json')==rec
            assert at(folder/(m.rsplit('.',1)[-1]+'.lean'))==src
            assert rec['warnings']==log.decode().count('warning:')==0
            assert [list(x)for x in found]==rec['reports']
        if m in overrides:
            assert entry['source_sha256']==overrides[m]['source_sha256'] and entry['imports']==overrides[m]['imports']
    for origin,key in [('phase9_fresh','fresh_modules'),('phase8_checked','phase8_reused_modules'),('isolated_checked','isolated_reused_modules')]:
        assert origins[origin]==result[key]
    executable_paths={toolchain[k]['path']for k in ('lean','lake','Init.olean')}
    for path,pin in before['inputs'].items():
        if not binary_name(path) and path not in executable_paths:assert digest(at(path))==pin,path
    ready=done[TARGETS[0]]
    assert ready['origin']=='phase9_fresh'
    assert [n for n,_ in reports(at(ready['log']))]==['SetTheory.BusyBeaver.ZFC.KHomeReadyControls.'+n for n in NAMES]
    for m in TARGETS[2:]:assert done[m]['origin']=='phase9_fresh'
    runtime=done[TARGETS[1]]
    expected=['SetTheory.BusyBeaver.ZFC.'+n for n in ('KHomeRuntimeAudit.original_executor','KRuntimeCore.exec_sound','KRuntimeCore.execWith_sound')]
    assert overrides[TARGETS[1]]['reports']==expected
    assert [n for n,_ in reports(at(runtime['log']))]==expected
    return {'status':'PASS_SEPARATE_AUXILIARY_RECORDS','modules':18,'targets':TARGETS,
            'fresh_modules':len(origins['phase9_fresh']),'isolated_reused_modules':len(origins['isolated_checked']),
            'phase8_reused_modules':len(origins['phase8_checked']),'fresh_ready_reports':5,'original_executor_reports':3,
            'result_sha256':configuration['auxiliary_result_sha256'],
            'scope':'Separate readiness/fallback controls and exact old-executor/KEngine224/KEngine225 compatibility check. Not a full legacy closure refresh.'}
