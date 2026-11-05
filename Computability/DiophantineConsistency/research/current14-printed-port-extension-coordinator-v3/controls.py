#!/usr/bin/env python3
"""No-Lean controls for the outer-exit coordinator and terminal verifier."""
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
if OUT.exists():raise SystemExit('refusing existing controls observation')
spec=importlib.util.spec_from_file_location('coordinator_controls',HERE/'coordinator.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
results={}
def expect(label,fn,needle):
    try:fn()
    except Exception as exc:
        if needle not in repr(exc):raise
        results[label]=repr(exc)
    else:raise RuntimeError('unexpected acceptance '+label)
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='current14-coordinator-controls-') as d:
    root=Path(d);ext=root/'extension';workspace=root/'workspace';overlay=ext/'lib';src=ext/'src';logs=ext/'logs'
    for p in (overlay,src,logs,workspace):p.mkdir(parents=True,exist_ok=True)
    names=['Synthetic.M'+str(i) for i in range(61)];rows={};records=[];outputs={}
    for i,name in enumerate(names):
        rel=name.replace('.','/');s=src/(rel+'.lean');w=workspace/(rel+'.lean');o=overlay/(rel+'.olean')
        for p in (s,w,o):p.parent.mkdir(parents=True,exist_ok=True)
        s.write_text('source '+str(i));w.write_bytes(s.read_bytes());o.write_bytes(('object '+str(i)).encode())
        log=logs/(f'{i:03d}-'+name.replace('.','_')+'.log');log.write_text('')
        rows[name]={'workspace_path':str(w.relative_to(workspace)),'sha256':digest(s),'imports':[]}
        depout=logs/(f'{i:03d}-'+name.replace('.','_')+'.deps.stdout');depout.write_text('')
        deperr=logs/(f'{i:03d}-'+name.replace('.','_')+'.deps.stderr');deperr.write_text('')
        receipt={'pid':6000+i,'initial':{'ppid':4242,'pgrp':6000+i,'session':6000+i,'start':123},
                 'session_drained':True,'direct_child_reaped':True,'exit':0}
        records.append({'module':name,'exit':0,'source_sha256':digest(s),'object_sha256':digest(o),
                        'log':str(log),'log_sha256':digest(log),'direct_inputs':{},
                        'deps_stdout':str(depout),'deps_stdout_sha256':digest(depout),
                        'deps_stderr':str(deperr),'deps_stderr_sha256':digest(deperr),
                        'deps_receipt':receipt,'compile_receipt':receipt})
        outputs[name]=c.driver.scan(Path(str(o)[:-6]))
    # A real project dependency in the synthetic overlay exercises the
    # success path for nonempty --deps output and authenticated routing.
    dependency=overlay/'Synthetic/M0.olean'
    rows[names[1]]['imports']=[names[0]]
    records[1]['direct_inputs']={names[0]:{'path':str(dependency),'kind':'project','sha256':digest(dependency)}}
    depout=Path(records[1]['deps_stdout']);depout.write_text(str(dependency)+'\n')
    records[1]['deps_stdout_sha256']=digest(depout)
    tool=root/'tool';tool.mkdir();init=tool/'Init.olean';init.write_bytes(b'synthetic-init')
    records[1]['direct_inputs']['Init']={'path':str(init),'kind':'toolchain','sha256':digest(init)}
    depout.write_text(str(init)+'\n'+str(init)+'\n'+str(dependency)+'\n')
    records[1]['deps_stdout_sha256']=digest(depout)
    external_guard=c.driver.scan(tool/'Init')
    ctx={'order':names,'rows':rows,'base':{'outputs':{}},'base_lib':root/'base-lib',
         'manifest':{'sources':{}},'external':['Init'],'external_guard':external_guard,'workspace_root':workspace,
         'package_root':root/'package','tool_root':root/'tool'}
    hashes={'driver_sha256':'synthetic-driver','guards_sha256':'synthetic-guards','owned_sha256':'synthetic-owned','deps_sha256':'synthetic-deps'}
    state={'status':'PASS','phase':'complete',**hashes,'records':records,'outputs':outputs,
           'base_overlay_guards':{},'external_guards':external_guard,'overlay_external_guards':c.driver.scan(overlay/'Init')}
    helpers={'need':c.need,'digest':c.driver.digest,'check_guard':c.driver.check_guard,'suffixes':c.driver.SUFFIXES}
    good=c.verify_terminal(state,0,ctx,ext,helpers,hashes,4242)
    if good['rows']!=61:raise RuntimeError('synthetic terminal success has wrong count')
    results['synthetic_61_row_terminal_accepted']=good['rows']
    expect('nonzero_outer_exit_rejected',lambda:c.verify_terminal(state,1,ctx,ext,helpers,hashes,4242),'extension did not exit successfully')
    original_dep=depout.read_text()
    for label,value in [('third_init_rejected',str(init)+'\n'+original_dep),
                        ('duplicate_project_rejected',original_dep+str(dependency)+'\n'),
                        ('alternate_init_rejected',original_dep+'/other/Init.olean\n')]:
        depout.write_text(value);badrec=dict(records[1]);badrec['deps_stdout_sha256']=digest(depout)
        bad=dict(state);bad['records']=[records[0],badrec]+records[2:]
        expect(label,lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),
               'unrecorded dependency path' if label=='alternate_init_rejected' else 'duplicate or conflicting import')
    depout.write_text(original_dep)

    bad=dict(state);bad['records']=records[:-1]
    expect('missing_row_rejected',lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),'incomplete or failed extension rows')
    bad=dict(state);bad['driver_sha256']='forged'
    expect('terminal_pin_mismatch_rejected',lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),'terminal pin mismatch')
    badrec=dict(records[0]);badreceipt=dict(badrec['deps_receipt']);badreceipt['session_drained']=False
    badrec['deps_receipt']=badreceipt;bad=dict(state);bad['records']=[badrec]+records[1:]
    expect('undrained_session_rejected',lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),'owned session receipt mismatch')
    expect('wrong_driver_parent_rejected',lambda:c.verify_terminal(state,0,ctx,ext,helpers,hashes,9999),'owned session receipt mismatch')
    badrec=dict(records[0]);badreceipt=dict(badrec['compile_receipt']);badreceipt['direct_child_reaped']=False
    badrec['compile_receipt']=badreceipt;bad=dict(state);bad['records']=[badrec]+records[1:]
    expect('unreaped_child_rejected',lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),'owned session receipt mismatch')
    badrec=dict(records[0]);badreceipt=dict(badrec['compile_receipt']);badreceipt['exit']=1
    badrec['compile_receipt']=badreceipt;bad=dict(state);bad['records']=[badrec]+records[1:]
    expect('inner_failure_rejected',lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),'owned session receipt mismatch')
    deppath=Path(records[0]['deps_stdout']);deppath.write_text('injected')
    expect('mutated_deps_log_rejected',lambda:c.verify_terminal(state,0,ctx,ext,helpers,hashes,4242),'deps log mismatch')
    deppath.write_text('')
    first=overlay/'Synthetic/M0.olean';original=first.read_bytes();first.write_bytes(b'changed')
    expect('mutated_output_rejected',lambda:c.verify_terminal(state,0,ctx,ext,helpers,hashes,4242),'output mismatch')
    first.write_bytes(original)
    firstsrc=src/'Synthetic/M0.lean';original=firstsrc.read_bytes();firstsrc.write_bytes(b'changed')
    expect('mutated_source_rejected',lambda:c.verify_terminal(state,0,ctx,ext,helpers,hashes,4242),'source mismatch')
    firstsrc.write_bytes(original)
    companion=overlay/'Synthetic/M0.ilean';companion.write_bytes(b'unexpected')
    expect('unexpected_companion_rejected',lambda:c.verify_terminal(state,0,ctx,ext,helpers,hashes,4242),'unexpected or missing extension overlay file')
    companion.unlink()
    extra=overlay/'foreign.olean';extra.write_bytes(b'unexpected')
    expect('unexpected_overlay_file_rejected',lambda:c.verify_terminal(state,0,ctx,ext,helpers,hashes,4242),'unexpected or missing extension overlay file')
    extra.unlink()
    shadowctx=dict(ctx);shadowctx['external']=['Mathlib.Tactic']
    shadowstate=dict(state);shadowstate['overlay_external_guards']=c.driver.scan(overlay/'Mathlib/Tactic')
    (overlay/'Mathlib').mkdir()
    expect('external_namespace_shadow_rejected',lambda:c.verify_terminal(shadowstate,0,shadowctx,ext,helpers,hashes,4242),'external namespace shadow')
    (overlay/'Mathlib').rmdir()
    badrec=dict(records[0]);badrec['direct_inputs']={'Unexpected.Module':{'path':'/unexpected'}}
    bad=dict(state);bad['records']=[badrec]+records[1:]
    expect('unexpected_import_rejected',lambda:c.verify_terminal(bad,0,ctx,ext,helpers,hashes,4242),'missing dependency paths')
actual=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'coordinator.py'),'--check'],capture_output=True,text=True,timeout=120)
if actual.returncode!=0 or 'PREFLIGHT_ONLY' not in actual.stdout or c.OUT.exists() or c.driver.OUT.exists():
    raise RuntimeError('actual post-base preflight did not succeed cleanly: '+actual.stderr)
results['actual_post_base_preflight_exit']=actual.returncode
optimized=subprocess.run([sys.executable,'-I','-O','-S','-B',str(HERE/'coordinator.py'),'--check'],capture_output=True,text=True,timeout=30)
if optimized.returncode==0 or 'refusing optimized Python' not in optimized.stderr:raise RuntimeError('optimized Python accepted')
results['optimized_python_refused']=optimized.stderr.strip()
class FakeLiveChild:
    def poll(self):return None
    def wait(self):return 17
fake_state={};snapshots=[]
c.settle_monitor_failure(FakeLiveChild(),fake_state,lambda:snapshots.append(dict(fake_state)),RuntimeError('sample failure'))
if snapshots[0]['status']!='MONITOR_FAILURE_WAITING_FOR_CHILD' or fake_state['child_exit_after_monitor_failure']!=17:
    raise RuntimeError('live-child monitor-failure handling did not wait and record')
results['monitor_failure_waits_for_child']=True
class InterruptOnceChild:
    def __init__(self):self.waits=0
    def wait(self):
        self.waits+=1
        if self.waits==1:raise RuntimeError('injected transient wait failure')
        return 19
child=InterruptOnceChild();bad_save_state={}
def failing_save():raise RuntimeError('injected emergency save failure')
c.settle_monitor_failure(child,bad_save_state,failing_save,RuntimeError('sample failure'))
if child.waits!=2 or bad_save_state['child_exit_after_monitor_failure']!=19:
    raise RuntimeError('monitor failure escaped before waiting for child')
results['emergency_save_and_wait_exceptions_still_wait']=True
receipt={'status':'PASS','controls':results,'coordinator_sha256':digest(HERE/'coordinator.py'),
         'verify_sha256':digest(HERE/'verify.py'),'scope':'Synthetic terminal and refusal controls; no Lean or real extension launch.'}
with OUT.open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(receipt,sort_keys=True))
