#!/usr/bin/env python3
"""Non-Lean refusal and guard controls; all fixtures live in a temporary root."""
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path

if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent
OUT=HERE/'controls-observation.json'
if OUT.exists():raise SystemExit('refusing existing control observation')
spec=importlib.util.spec_from_file_location('extension_driver_control',HERE/'driver.py')
driver=importlib.util.module_from_spec(spec);spec.loader.exec_module(driver)
results={}
def expect(label,fn,needle):
    try:fn()
    except Exception as exc:
        if needle not in repr(exc):raise
        results[label]=repr(exc)
    else:raise RuntimeError('control unexpectedly accepted '+label)
def write(p,v):p.write_text(json.dumps(v,sort_keys=True))
with tempfile.TemporaryDirectory(prefix='current14-extension-controls-') as d:
    root=Path(d);driver.WATCHDOG=root/'watchdog.json';driver.BASE_STATE=root/'state.json'
    driver.OUT=root/'output';driver.SNAP=root/'snapshot';driver.SNAP.mkdir()
    write(driver.SNAP/'manifest.json',{})
    driver.PINS[driver.SNAP/'manifest.json']=driver.digest(driver.SNAP/'manifest.json')
    provider=driver.PINS[driver.PROVIDER]
    driver.BASE_STATE.write_text('{}')
    write(driver.WATCHDOG,{'status':'RUNNING'})
    old=sys.argv;sys.argv=[str(HERE/'driver.py'),'--run']
    try:expect('running_base_run_refused',driver.main,'base watchdog has not completed successfully')
    finally:sys.argv=old
    if driver.OUT.exists():raise RuntimeError('refusal created an output')
    wd={'status':'PASS','exit':0,'build_status':'PASS','build_source_status':'CURRENT_AT_FINAL_CHECK',
        'build_source_drift':[],'snapshot_sha256':driver.PINS[driver.SNAP/'manifest.json'],'provider_sha256':provider,
        'runner_sha256':'790a4b13f96f5cd544981aab6bdc7ae9e573a32f14195505551e191f0ee0a212',
        'driver_sha256':'8170bd401b1821666fffc2a55f8dd908e473d32c71797661a5acd85a32d0dc56',
        'build_state_sha256':'0'*64}
    write(driver.WATCHDOG,wd)
    expect('stale_base_state_refused',driver.base_gate,'base state differs from watchdog')
    names=['Synthetic.M'+str(i) for i in range(999)]+['DiophantineConsistency.IPRAStandardCurrentEndpointChecks']
    manifest={'order':names,'target':'DiophantineConsistency.IPRAStandardCurrentEndpointChecks',
              'lakefile_sha256':driver.digest(driver.ROOT/'lakefile.toml'),
              'lean_toolchain_sha256':driver.digest(driver.ROOT/'lean-toolchain')}
    write(driver.SNAP/'manifest.json',manifest)
    driver.PINS[driver.SNAP/'manifest.json']=driver.digest(driver.SNAP/'manifest.json')
    wd['snapshot_sha256']=driver.PINS[driver.SNAP/'manifest.json']
    state={'status':'PASS','source_status':'CURRENT_AT_FINAL_CHECK','workspace_source_drift':[],
           'manifest_sha256':driver.PINS[driver.SNAP/'manifest.json'],'provider_receipt_sha256':provider,
           'lean_sha256':driver.PINS[driver.LEAN],'package_overlay':str(driver.PKG),
           'driver_sha256':wd['driver_sha256'],
           'records':[{'module':n,'exit':1 if i==30 else 0} for i,n in enumerate(names)],
           'outputs':{n:{} for n in names}}
    write(driver.BASE_STATE,state);wd['build_state_sha256']=driver.digest(driver.BASE_STATE);write(driver.WATCHDOG,wd)
    expect('failed_base_row_refused',driver.base_gate,'base row order or exit failure')
    wd['build_source_status']='HISTORICAL_SNAPSHOT';write(driver.WATCHDOG,wd)
    expect('source_drift_refused',driver.base_gate,'base was not source-current')
    wd['build_source_status']='CURRENT_AT_FINAL_CHECK'
    (root/'lakefile.toml').write_bytes((driver.ROOT/'lakefile.toml').read_bytes())
    (root/'lean-toolchain').write_bytes((driver.ROOT/'lean-toolchain').read_bytes())
    driver.ROOT=root;driver.BASE_DIR=root/'base'
    (root/'workspace.lean').write_text('expected source')
    relative='src/'+names[0].replace('.','/')+'.lean'
    frozen=driver.SNAP/relative;frozen.parent.mkdir(parents=True);frozen.write_text('tampered source')
    expected_source=driver.digest(root/'workspace.lean')
    manifest['sources']={names[0]:{'snapshot_path':relative,'workspace_path':'workspace.lean','sha256':expected_source,'imports':[]}}
    write(driver.SNAP/'manifest.json',manifest);driver.PINS[driver.SNAP/'manifest.json']=driver.digest(driver.SNAP/'manifest.json')
    wd['snapshot_sha256']=driver.PINS[driver.SNAP/'manifest.json'];state['manifest_sha256']=wd['snapshot_sha256']
    state['records']=[{'module':n,'exit':0,'source_sha256':expected_source,'object_sha256':'0'*64} for n in names]
    write(driver.BASE_STATE,state);wd['build_state_sha256']=driver.digest(driver.BASE_STATE);write(driver.WATCHDOG,wd)
    expect('tampered_base_source_refused',driver.base_gate,'base source drift')
    frozen.write_text('expected source')
    objpath=driver.BASE_DIR/'lib/Synthetic/M0.olean';objpath.parent.mkdir(parents=True);objpath.write_bytes(b'tampered object')
    stem=Path(str(objpath)[:-6]);state['outputs'][names[0]]={str(stem)+s:None for s in driver.SUFFIXES}
    state['outputs'][names[0]][str(objpath)]={'realpath':str(objpath),'sha256':'0'*64}
    write(driver.BASE_STATE,state);wd['build_state_sha256']=driver.digest(driver.BASE_STATE);write(driver.WATCHDOG,wd)
    expect('tampered_base_object_refused',driver.base_gate,'base object mismatch')
    # Exercise the complete base gate with 1,000 tiny synthetic modules, then
    # forge a target log while keeping its ledger and watchdog hashes coherent.
    driver.PKG=root/'package';driver.PKG.mkdir();init=driver.PKG/'Init.olean';init.write_bytes(b'init')
    source_rows={};records=[];outputs={};logdir=root/'logs';logdir.mkdir()
    axiom_names=['DiophantineConsistency.IPRAStandardTheory.leibniz',
                 'DiophantineConsistency.IPRAStandardTheory.provable_iff',
                 'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency',
                 'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency']
    axiom_text=''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in axiom_names)
    for i,n in enumerate(names):
        rel=n.replace('.','/');snap=driver.SNAP/'src'/(rel+'.lean');workspace=root/'workspace'/(rel+'.lean')
        snap.parent.mkdir(parents=True,exist_ok=True);workspace.parent.mkdir(parents=True,exist_ok=True)
        snap.write_text('synthetic source '+str(i));workspace.write_bytes(snap.read_bytes())
        source_rows[n]={'snapshot_path':str(snap.relative_to(driver.SNAP)),
                        'workspace_path':str(workspace.relative_to(root)),
                        'sha256':driver.digest(snap),'imports':[]}
        obj=driver.BASE_DIR/'lib'/(rel+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);obj.write_bytes(('object '+str(i)).encode())
        log=logdir/(str(i)+'.log');log.write_text(axiom_text if i==999 else '')
        records.append({'module':n,'exit':0,'source_sha256':driver.digest(snap),'object_sha256':driver.digest(obj),
                        'log':str(log),'log_sha256':driver.digest(log),
                        'direct_inputs':{'Init':{'path':str(init),'kind':'package','sha256':driver.digest(init)}},
                        'axiom_reports':['propext, Classical.choice, Quot.sound']*4 if i==999 else []})
        outputs[n]=driver.scan(Path(str(obj)[:-6]))
    manifest['sources']=source_rows;write(driver.SNAP/'manifest.json',manifest)
    driver.PINS[driver.SNAP/'manifest.json']=driver.digest(driver.SNAP/'manifest.json')
    wd['snapshot_sha256']=driver.PINS[driver.SNAP/'manifest.json']
    state.update(manifest_sha256=wd['snapshot_sha256'],package_overlay=str(driver.PKG),records=records,
                 outputs=outputs,guarded_companions=driver.scan(driver.PKG/'Init'))
    write(driver.BASE_STATE,state);wd['build_state_sha256']=driver.digest(driver.BASE_STATE);write(driver.WATCHDOG,wd)
    _,passed_state,passed_manifest=driver.base_gate()
    if len(passed_state['records'])!=1000 or passed_manifest['order']!=names:
        raise RuntimeError('synthetic base success returned wrong rows')
    results['synthetic_complete_base_accepted']='1000 source, object, log and guard rows'
    target_log=Path(records[-1]['log']);target_log.write_text(axiom_text.replace(axiom_names[0],axiom_names[0]+'_forged'))
    state['records'][-1]['log_sha256']=driver.digest(target_log)
    write(driver.BASE_STATE,state);wd['build_state_sha256']=driver.digest(driver.BASE_STATE);write(driver.WATCHDOG,wd)
    expect('forged_target_axiom_log_rejected',driver.base_gate,'base endpoint axiom reports differ from log')
    stem=root/'data';obj=Path(str(stem)+'.olean');obj.write_bytes(b'first')
    g=driver.scan(stem);driver.check_guard(g);obj.write_bytes(b'changed')
    expect('mutated_object_rejected',lambda:driver.check_guard(g),'input changed')
    obj.write_bytes(b'first');Path(str(stem)+'.ilean').write_bytes(b'unexpected')
    expect('unexpected_companion_rejected',lambda:driver.check_guard(g),'unexpected file')
    first=root/'first-object';second=root/'second-object';first.write_bytes(b'same');second.write_bytes(b'same')
    linkstem=root/'symlink-test';link=Path(str(linkstem)+'.olean');link.symlink_to(first)
    linkguard=driver.scan(linkstem);link.unlink();link.symlink_to(second)
    expect('same_bytes_symlink_swap_rejected',lambda:driver.check_guard(linkguard),'input changed')
    producer=root/'producer.olean';producer.write_bytes(b'original producer');produced_sha=driver.digest(producer)
    driver.capture_output(producer,produced_sha);producer.write_bytes(b'changed producer')
    expect('producer_record_capture_mismatch_rejected',lambda:driver.capture_output(producer,produced_sha),
           'producer object differs from recorded output')
    direct=root/'direct.olean';direct.write_bytes(b'original direct');direct_sha=driver.digest(direct)
    driver.capture_input(direct,direct_sha);direct.write_bytes(b'changed direct')
    expect('direct_record_capture_mismatch_rejected',lambda:driver.capture_input(direct,direct_sha),
           'direct object differs from recorded input')
    fallback=root/'fallback';fallback.mkdir();(fallback/'DiophantineConsistency').mkdir()
    expect('project_shadow_rejected',lambda:driver.reject_project_fallbacks((fallback,),{'DiophantineConsistency'}),'project fallback')
    (fallback/'Mathlib').mkdir()
    expect('external_namespace_shadow_rejected',lambda:driver.reject_project_fallbacks((fallback,),{'Mathlib'}),'project fallback')
optimized=subprocess.run([sys.executable,'-I','-O','-S','-B',str(HERE/'driver.py'),'--check'],capture_output=True,text=True,timeout=30)
if optimized.returncode==0 or 'refusing optimized Python' not in optimized.stderr:raise RuntimeError('optimized mode accepted')
results['optimized_python_refused']=optimized.stderr.strip()
results['no_lean_invoked']=True
receipt={'status':'PASS','controls':results,
         'driver_sha256':hashlib.sha256((HERE/'driver.py').read_bytes()).hexdigest(),
         'guards_sha256':hashlib.sha256((HERE/'guards.py').read_bytes()).hexdigest(),
         'scope':'Synthetic gate/guard rejection controls; no successful extension run or Lean invocation.'}
with OUT.open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(receipt,sort_keys=True))
