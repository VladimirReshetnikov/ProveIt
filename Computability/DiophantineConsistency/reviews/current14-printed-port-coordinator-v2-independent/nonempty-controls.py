#!/usr/bin/env python3
"""Exercise the terminal verifier with actual synthetic dependency routes, no Lean."""
import copy,hashlib,importlib.util,json,sys,tempfile
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
base=Path(__file__).resolve().parents[2]/'research'
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod
verify=load('ext_verify',base/'current14-printed-port-extension-coordinator-v2'/'verify.py')
g=load('ext_guards',base/'current14-printed-port-extension-driver-v2'/'guards.py')
def need(x,msg):
    if not x:raise ValueError(msg)
def expect(fn,part):
    try:fn()
    except Exception as e:
        if part not in repr(e):raise
        return repr(e)
    raise RuntimeError('unexpected acceptance: '+part)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='independent-extension-routes-') as tmp:
    root=Path(tmp);ext=root/'extension';overlay=ext/'lib';src=ext/'src';logs=ext/'logs';workspace=root/'workspace';base_lib=root/'base';tool=root/'tool';pkg=root/'pkg'
    for p in (overlay,src,logs,workspace,base_lib,tool,pkg):p.mkdir(parents=True,exist_ok=True)
    bo=base_lib/'Base/M.olean';bo.parent.mkdir(parents=True);bo.write_bytes(b'base-object')
    ob=overlay/'Base/M.olean';ob.parent.mkdir(parents=True);ob.symlink_to(bo)
    ti=tool/'Init.olean';ti.write_bytes(b'tool-init')
    baseguard=g.scan(base_lib/'Base/M');eg=g.scan(tool/'Init');shadow=g.scan(overlay/'Init')
    names=['Synthetic.M'+str(i) for i in range(61)];rows={};outputs={};records=[]
    for i,name in enumerate(names):
        rel=name.replace('.','/'); staged=src/(rel+'.lean'); w=workspace/(rel+'.lean'); o=overlay/(rel+'.olean')
        for p in (staged,w,o):p.parent.mkdir(parents=True,exist_ok=True)
        staged.write_text('source '+name);w.write_bytes(staged.read_bytes());o.write_text('object '+name)
        outputs[name]=g.scan(Path(str(o)[:-6]))
        if i==0:direct={'Init':{'path':str(ti),'kind':'toolchain','sha256':sha(ti)},'Base.M':{'path':str(ob),'kind':'project','sha256':sha(ob)}}
        else:
            prev=overlay/(names[i-1].replace('.','/')+'.olean')
            direct={names[i-1]:{'path':str(prev),'kind':'project','sha256':sha(prev)}}
        rows[name]={'workspace_path':str(w.relative_to(workspace)),'sha256':sha(staged),'imports':list(direct)}
        stem=logs/(f'{i:03d}-'+name.replace('.','_'));log=Path(str(stem)+'.log');log.write_text('')
        depout=Path(str(stem)+'.deps.stdout');depout.write_text(''.join(v['path']+'\n' for v in direct.values()))
        deperr=Path(str(stem)+'.deps.stderr');deperr.write_text('')
        pid=6000+2*i
        def receipt(p):return {'pid':p,'initial':{'ppid':4242,'pgrp':p,'session':p,'start':123+p},'session_drained':True,'direct_child_reaped':True,'exit':0}
        records.append({'module':name,'exit':0,'source_sha256':sha(staged),'object_sha256':sha(o),
             'log':str(log),'log_sha256':sha(log),'direct_inputs':direct,
             'deps_stdout':str(depout),'deps_stdout_sha256':sha(depout),'deps_stderr':str(deperr),'deps_stderr_sha256':sha(deperr),
             'deps_receipt':receipt(pid),'compile_receipt':receipt(pid+1)})
    ctx={'order':names,'rows':rows,'base':{'outputs':{'Base.M':baseguard}},'base_lib':base_lib,
         'manifest':{'sources':{'Base.M':{}}},'external':['Init'],'external_guard':eg,
         'workspace_root':workspace,'package_root':pkg,'tool_root':tool}
    expectedbase={str(overlay/Path(path).relative_to(base_lib)):entry for path,entry in baseguard.items()}
    hashes={'driver_sha256':'synthetic-driver','guards_sha256':'synthetic-guards','owned_sha256':'synthetic-owned'}
    state={'status':'PASS','phase':'complete',**hashes,'records':records,'outputs':outputs,
           'base_overlay_guards':expectedbase,'external_guards':eg,'overlay_external_guards':shadow}
    helpers={'need':need,'digest':g.digest,'check_guard':g.check_guard,'suffixes':g.SUFFIXES}
    def check(s=state):return verify.verify_terminal(s,0,ctx,ext,helpers,hashes,4242)
    good=check();need(good['rows']==61,'bad row count')
    results={'nonempty_61_row_terminal_accepted':True,'direct_base_symlink':True,'toolchain_Init':True,'fresh_project_chain':60}
    bad=copy.deepcopy(state);bad['records'][1]['direct_inputs'][names[0]]['sha256']='0'*64
    results['wrong_producer_hash_rejected']=expect(lambda:check(bad),'direct producer mismatch')
    bad=copy.deepcopy(state);bad['records'][1]['direct_inputs'][names[0]]['path']=str(ti)
    dep=Path(bad['records'][1]['deps_stdout']);original=dep.read_bytes();dep.write_text(str(ti)+'\n');bad['records'][1]['deps_stdout_sha256']=sha(dep)
    results['wrong_project_route_rejected']=expect(lambda:check(bad),'project route mismatch');dep.write_bytes(original)
    bad=copy.deepcopy(state);bad['records'][0]['deps_receipt']['initial']['pgrp']+=1
    results['wrong_owned_group_rejected']=expect(lambda:check(bad),'owned session receipt mismatch')
    bad=copy.deepcopy(state);bad['records'][1]['direct_inputs']['Unlisted']={'path':'/unlisted','kind':'project','sha256':'x'}
    dep=Path(bad['records'][1]['deps_stdout']);original=dep.read_bytes();dep.write_bytes(original+b'/unlisted\n');bad['records'][1]['deps_stdout_sha256']=sha(dep)
    results['extra_import_rejected']=expect(lambda:check(bad),'direct imports mismatch');dep.write_bytes(original)
    extra=overlay/'unexpected.olean';extra.write_bytes(b'x')
    results['extra_inventory_rejected']=expect(check,'unexpected or missing extension overlay file');extra.unlink()
    need(check()['rows']==61,'restored case failed')
    out={'status':'PASS_SYNTHETIC_NONEMPTY_ROUTES','script_sha256':sha(__file__),
         'verifier_sha256':sha(base/'current14-printed-port-extension-coordinator-v2'/'verify.py'),
         'guards_sha256':sha(base/'current14-printed-port-extension-driver-v2'/'guards.py'),
         'controls':results,'scope':'Synthetic terminal verification only; no Lean, coordinator launch, or live base evidence.'}
    print(json.dumps(out,indent=2,sort_keys=True))
