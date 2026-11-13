#!/usr/bin/env python3
"""Guarded two-client source build atop one authenticated v2 extension."""
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1];ROOT=HERE.parents[3]
COORD=TASK/'research/current14-printed-port-extension-coordinator-v3/coordinator.py'
VERIFY=COORD.parent/'verify.py'
SUP=HERE/'extension_supervisor.py'; OWNED=HERE/'owned.py'
SUP_OUT=Path('/tmp/current14-printed-port-coordinator-supervisor-v3-20261104')
OUT=Path('/tmp/current14-structured-endpoint-coherent-v3-20261104')
PINS={COORD:'83dfc99170172bb241936e96f7466cd292a0e523a1e01a4e0e1cc4406fae2a1e',
      VERIFY:'068e9d3531cb593cc73c60239d0637e305efb2dcd0cdfa5c43a4a98c9a5a0109',
      SUP:'8a95015a6f7832f2ec3231b710cb6d03f4da3efa7985138a055597164a030dad',
      OWNED:'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498',
      TASK/'research/current14-literal-port-assembly/Current14LiteralPorts.lean':'b19dfc3f5ea1639dcd6003613cd587992d3ab64f707cbe7c9fb61a466092f8b0',
      TASK/'research/current14-structured-endpoint-draft/StructuredEndpoint.lean':'31b2869c63f33610beac36cec7bcbcbcbfc00579b106fbc130ce0f754702a392'}
CLIENTS=[('Current14LiteralPorts',['DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.CurrentMaskRecipes2011'],
          ['Current14LiteralPorts.beta_eq','Current14LiteralPorts.mu_eq','Current14LiteralPorts.omega_eq','Current14LiteralPorts.K_eq','Current14LiteralPorts.all_ports']),
         ('StructuredEndpoint',['Current14LiteralPorts','DiophantineConsistency.IPRAStandardCurrentEndpoint'],
          ['Current14StructuredEndpoint.recipe_endpoint'])]
SOURCES=[TASK/'research/current14-literal-port-assembly/Current14LiteralPorts.lean',TASK/'research/current14-structured-endpoint-draft/StructuredEndpoint.lean']
MIN_MEMORY=10*1024**3;MAX_RSS=7*1024**3;MIN_DISK=4_000_000_000

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def need(c,m):
    if not c:raise ValueError(m)
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def pin():
    for p,h in PINS.items():need(p.is_file() and sha(p)==h,('pin mismatch',str(p)))
def read(path):return json.loads(Path(path).read_text())
def authenticate():
    pin()
    c=load('structured_extension_coordinator',COORD);ctx=c.context();driver=c.driver
    receipt=read(SUP_OUT/'receipt.json'); statepath=c.OUT/'state.json';cs=read(statepath)
    need(receipt.get('status')=='PASS' and receipt.get('child_exit')==0 and not receipt.get('wait_interruptions'), 'coordinator outer exit not successful')
    need(receipt.get('coordinator_sha256')==PINS[COORD] and receipt.get('verify_sha256')==PINS[VERIFY] and
         receipt.get('supervisor_sha256')==PINS[SUP] and receipt.get('coordinator_state_sha256')==sha(statepath), 'coordinator supervisor pin mismatch')
    log=SUP_OUT/'coordinator.log';need(receipt.get('log')==str(log) and sha(log)==receipt.get('log_sha256'), 'supervisor log mismatch')
    need(cs.get('status')=='PASS' and cs.get('child_exit')==0 and cs.get('coordinator_sha256')==PINS[COORD] and
         cs.get('verify_sha256')==PINS[VERIFY] and cs.get('initial_hashes')==c.final_hashes(),'coordinator terminal mismatch')
    extstate=driver.OUT/'state.json';need(cs.get('extension_state_sha256')==sha(extstate),'extension terminal digest mismatch')
    elog=c.OUT/'extension-process.log';need(sha(elog)==cs.get('process_log_sha256'),'extension process log mismatch')
    helper={'need':c.need,'digest':driver.digest,'check_guard':driver.check_guard,'suffixes':driver.SUFFIXES}
    ext=read(extstate);v=c.verify_terminal(ext,cs['child_exit'],ctx,driver.OUT,helper,cs['initial_hashes'],cs['child_pid'])
    need(v==cs.get('validation'),'extension terminal validation differs')
    pin();need(sha(statepath)==receipt['coordinator_state_sha256'] and sha(extstate)==cs['extension_state_sha256'],'terminal evidence changed')
    return c,ctx,ext,{'supervisor_receipt_sha256':sha(SUP_OUT/'receipt.json'),
                      'coordinator_state_sha256':sha(statepath),'extension_state_sha256':sha(extstate)}

def reports(text,expected):
    need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'error, warning or sorry pattern in Lean log')
    found=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
    need([name for name,_ in found]==expected,('axiom names mismatch',found,expected))
    allowed={'propext','Classical.choice','Quot.sound'}
    need(all(not ({x.strip() for x in axioms.split(',') if x.strip()}-allowed) for _,axioms in found),'unexpected axiom')
    return found

def run(ctx,c,ext,initial):
    driver=c.driver;need(not OUT.exists() and c.idle_lean(),'output exists or Lean slot busy')
    owned=load('structured_owned',OWNED);runner_sha=sha(__file__);owned_sha=sha(OWNED)
    OUT.mkdir();src=OUT/'src';src.mkdir();lib=OUT/'lib';lib.mkdir();logs=OUT/'logs';logs.mkdir()
    state={'status':'RUNNING','runner_sha256':runner_sha,'owned_sha256':owned_sha,'initial':initial,'records':[],
           'scope':'Two clients atop one authenticated extension; transitive/dynamic/transient ancestry inherited.'}
    def save():
        p=OUT/'state.tmp';p.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');p.replace(OUT/'state.json')
    save()
    try:
        for source,(name,_,_) in zip(SOURCES,CLIENTS):
            target=src/(name+'.lean');target.write_bytes(source.read_bytes());need(sha(target)==PINS[source] and sha(source)==PINS[source],'client source copy drift')
        env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(driver.OUT/'lib')+':'+str(driver.PKG),LEAN_NUM_THREADS='1')
        for var in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(var,None)
        tops=ctx['tops']|{n.split('.')[0] for n in ctx['external']}
        driver.reject_project_fallbacks((lib,),tops)
        own={}; project=driver.OUT/'lib'
        driver.reject_project_fallbacks((project,driver.PKG,driver.TOOL),{n for n,_,_ in CLIENTS})
        shadows={}
        for root in (project,driver.PKG,driver.TOOL):
            for name,_,_ in CLIENTS:
                g=driver.scan(root/name);need(all(v is None for v in g.values()),('client fallback shadow',str(root),name));shadows.update(g)
        def monitored(cmd,label,out,err,timeout=600):
            samples=[];started=time.monotonic()
            def check(pid):
                rss=0
                for member in owned.group_live(pid):
                    try:rss+=int(Path('/proc',str(member),'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
                    except FileNotFoundError:pass
                sample={'seconds':round(time.monotonic()-started,2),'session_rss_bytes':rss,
                        'memavailable_bytes':c.available(),'free_bytes':shutil.disk_usage('/tmp').free}
                samples.append(sample);state.update(phase=label,samples=samples);save()
                return sample['session_rss_bytes']<MAX_RSS and sample['memavailable_bytes']>=MIN_MEMORY and sample['free_bytes']>=MIN_DISK
            with out.open('x') as stdout,err.open('x') as stderr:
                code,seconds,receipt=owned.run(['ionice','-c3','nice','-n10',*cmd],cwd=src,env=env,stdout=stdout,stderr=stderr,
                                                timeout=timeout,disk_check=check,report=lambda msg:print(msg,flush=True))
            need(samples,'missing process resource sample')
            return code,seconds,receipt,samples
        for i,(name,declared,expected) in enumerate(CLIENTS):
            driver.reject_project_fallbacks((lib,),tops);driver.check_guard(shadows)
            source=src/(name+'.lean');depsout=logs/(name+'.deps.stdout');depserr=logs/(name+'.deps.stderr')
            dcode,dseconds,dreceipt,dsamples=monitored([str(driver.LEAN),'--deps',str(source)],name+' --deps',depsout,depserr)
            deps_text=depsout.read_text();deps_error=depserr.read_text()
            need(dcode==0 and not deps_error,'client deps failed')
            direct={};input_guards={};counts={}
            for line in deps_text.splitlines():
                path=Path(line);need(path.is_absolute() and path.is_file() and str(path).endswith('.olean'),'invalid client dependency')
                if path.is_relative_to(lib):
                    module=driver.logical_name(path,lib);need(module in own,'unbuilt client dependency');expected_guard=own[module]
                elif path.is_relative_to(project):
                    module=driver.logical_name(path,project)
                    if module in ctx['manifest']['sources']:
                        expected_guard={k:ext['base_overlay_guards'][k] for k in driver.scan(Path(str(path)[:-6]))}
                    else:expected_guard=ext['outputs'][module]
                elif path.is_relative_to(driver.PKG) or path.is_relative_to(driver.TOOL):
                    root=driver.PKG if path.is_relative_to(driver.PKG) else driver.TOOL
                    module=driver.logical_name(path,root);expected_guard={k:ctx['external_guard'][k] for k in driver.scan(Path(str(path)[:-6]))}
                else:raise ValueError(('dependency outside coherent roots',line))
                if driver.duplicate(direct,counts,module,path):continue
                observed=driver.capture_input(path,sha(path));need(observed==expected_guard,('client dependency differs from producer',module))
                direct[module]={'path':str(path),'sha256':observed[str(path)]['sha256']};input_guards.update(observed)
            driver.validate_dependencies(deps_text.splitlines(),direct)
            need(set(declared)<=set(direct) and not (set(direct)-set(declared)-{'Init'}),('client declared/direct mismatch',name))
            driver.check_guard(input_guards);driver.check_guard(shadows)
            obj=lib/(name+'.olean');log=logs/(name+'.lean.stdout');err=logs/(name+'.lean.stderr')
            cmd=[str(driver.LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(source),'-o',str(obj)]
            code,seconds,receipt,samples=monitored(cmd,name+' compile',log,err)
            log_text=log.read_text();err_text=err.read_text();need(code==0 and obj.is_file(),'client Lean failure')
            axioms=reports(log_text+'\n'+err_text,expected);objsha=sha(obj);own[name]=driver.capture_output(obj,objsha)
            driver.check_guard(input_guards);driver.check_guard(shadows)
            need(sha(source)==PINS[SOURCES[i]] and sha(SOURCES[i])==PINS[SOURCES[i]],'client source drift')
            need(depsout.read_text()==deps_text and depserr.read_text()==deps_error and
                 log.read_text()==log_text and err.read_text()==err_text,'client logs changed before recording')
            rec={'module':name,'exit':code,'seconds':seconds,'source_sha256':sha(source),'object_sha256':objsha,
                 'direct_inputs':direct,'direct_guards':input_guards,'output_guards':own[name],
                 'deps_stdout':str(depsout),'deps_stdout_sha256':sha(depsout),'deps_stderr':str(depserr),'deps_stderr_sha256':sha(depserr),
                 'log':str(log),'log_sha256':sha(log),'stderr':str(err),'stderr_sha256':sha(err),'axiom_reports':axioms,
                 'deps_receipt':dreceipt,'deps_samples':dsamples,'compile_receipt':receipt,'compile_samples':samples}
            need(depsout.read_text()==deps_text and depserr.read_text()==deps_error and
                 log.read_text()==log_text and err.read_text()==err_text,'client logs changed during recording')
            state['records'].append(rec);save()
        _,_,_,after=authenticate();need(after==initial,'authenticated extension changed')
        pin();need(sha(__file__)==runner_sha and sha(OWNED)==owned_sha,'runner changed')
        for i,rec in enumerate(state['records']):
            need(sha(SOURCES[i])==PINS[SOURCES[i]] and sha(src/(rec['module']+'.lean'))==PINS[SOURCES[i]],'final client source drift')
            for field in ('log','stderr','deps_stdout','deps_stderr'):need(sha(rec[field])==rec[field+'_sha256'],('log drift',field))
            driver.check_guard(rec['direct_guards']);driver.check_guard(rec['output_guards'])
        driver.check_guard(shadows);driver.reject_project_fallbacks((lib,),tops)
        driver.reject_project_fallbacks((project,driver.PKG,driver.TOOL),{n for n,_,_ in CLIENTS})
        expected_files={p for guard in own.values() for p,entry in guard.items() if entry is not None}
        actual_files={str(p) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
        need(actual_files==expected_files and not any(p.is_symlink() and p.is_dir() for p in lib.rglob('*')),
             'client output inventory mismatch')
        state.update(status='PASS',phase='complete',samples=[]);save();print('PASS two clients',flush=True)
    except BaseException as exc:
        state.update(status='FAILED',failure=repr(exc));save();raise

def main():
    p=argparse.ArgumentParser();p.add_argument('--run',action='store_true');p.parse_args()
    need(not OUT.exists(),'refusing existing client output')
    c,ctx,ext,initial=authenticate();need(c.idle_lean(),'Lean slot busy')
    print(json.dumps({'status':'PREFLIGHT_PASS','initial':initial},sort_keys=True),flush=True)
    if '--run' in sys.argv:run(ctx,c,ext,initial)
if __name__=='__main__':
    try:main()
    except Exception as exc:print('REFUSED_OR_FAILED',repr(exc),file=sys.stderr);raise SystemExit(1)
