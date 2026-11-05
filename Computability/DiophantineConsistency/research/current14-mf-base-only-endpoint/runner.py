#!/usr/bin/env python3
"""Guarded two-client source build atop authenticated fresh base only."""
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
DRIVER_DIR=TASK/'research/current14-printed-port-extension-driver-v3'
OWNED=TASK/'research/current14-structured-endpoint-coherent-runner-v3/owned.py'
OUT=Path('/tmp/current14-mf-base-only-attempt01-20261104')
PINS={DRIVER_DIR/'driver.py':'6e12ae1fae6e721238ac6a052428357049f060596fd51338811eee054aad0880',
      DRIVER_DIR/'guards.py':'e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3',
      DRIVER_DIR/'owned.py':'60859f538a7069d90f3f44871613fd2ef96c0ea738c9313cd1971d851b4b33ca',
      DRIVER_DIR/'deps.py':'d3f898f522e7d30756df4fb011b12beff44e338158d6d692e567caff748b8284',
      OWNED:'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498',
      HERE/'Current14LiteralPortsMF.lean':'8f7e7bc42f16d91ce118202467546160fb2364df4452a5b256ac8e1af7d00183',
      HERE/'StructuredEndpointMF.lean':'906861b83a51dd58b043da16a0d6628925128bfc1197568eb7ba09f472622a08'}
CLIENTS=[('Current14LiteralPortsMF',['DiophantineConsistency.MFCurrentKernel2011','DiophantineConsistency.ArithmeticMaskData','DiophantineConsistency.MFPaper1982Digits'],
          ['Current14LiteralPortsMF.beta_eq','Current14LiteralPortsMF.mu_eq','Current14LiteralPortsMF.omega_eq','Current14LiteralPortsMF.K_eq','Current14LiteralPortsMF.all_ports']),
         ('StructuredEndpointMF',['Current14LiteralPortsMF','DiophantineConsistency.IPRAStandardCurrentEndpoint'],
          ['Current14StructuredEndpointMF.recipe_endpoint'])]
SOURCES=[HERE/(name+'.lean') for name,_,_ in CLIENTS]
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
def available():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
    raise RuntimeError('MemAvailable unavailable')
def idle_lean():
    ps=subprocess.run(['ps','-eo','pid=,stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
    return not any(len(x)==3 and x[2]=='lean' and not x[1].startswith('Z') for x in (line.split() for line in ps.splitlines()))
def file_inventory(root):
    need(root.is_dir() and not root.is_symlink(),'invalid library root')
    actual_files=set()
    def walk_error(exc):
        raise exc
    for directory,dirs,files in os.walk(root,followlinks=False,onerror=walk_error):
        need(not any((Path(directory)/d).is_symlink() for d in dirs),'library contains symlink directory')
        for name in files:actual_files.add(str(Path(directory)/name))
    return actual_files

def check_base_inventory(base_lib,outputs):
    expected_files={p for guard in outputs.values() for p,entry in guard.items() if entry is not None}
    need(file_inventory(base_lib)==expected_files,'base library inventory differs from authenticated outputs')

def authenticate():
    pin();sys.path.insert(0,str(DRIVER_DIR))
    driver=load('base_driver',DRIVER_DIR/'driver.py');driver.pinned()
    wd,base,manifest=driver.base_gate();driver.provider_gate()
    check_base_inventory(driver.BASE_DIR/'lib',base['outputs'])
    tops={n.split('.')[0] for n in manifest['sources']}
    external_tops={n.split('.')[0] for n in manifest['external_modules']}
    driver.reject_project_fallbacks((driver.BASE_DIR/'lib',),external_tops-tops)
    driver.reject_project_fallbacks((driver.PKG,driver.TOOL),tops)
    need(available()>=MIN_MEMORY and shutil.disk_usage('/tmp').free>=MIN_DISK,'insufficient resources')
    initial={'base_state_sha256':sha(driver.BASE_STATE),'watchdog_sha256':sha(driver.WATCHDOG),
             'manifest_sha256':sha(driver.SNAP/'manifest.json'),'provider_sha256':sha(driver.PROVIDER)}
    need(initial['base_state_sha256']==wd['build_state_sha256'],'base state drift')
    pin();return driver,{'base':base,'manifest':manifest,'tops':tops},initial

def reports(text,expected):
    need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'error, warning or sorry pattern in Lean log')
    found=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
    need([name for name,_ in found]==expected,('axiom names mismatch',found,expected))
    allowed={'propext','Classical.choice','Quot.sound'}
    need(all(not ({x.strip() for x in axioms.split(',') if x.strip()}-allowed) for _,axioms in found),'unexpected axiom')
    return found

def run(driver,ctx,initial):
    need(not OUT.exists() and idle_lean(),'output exists or Lean slot busy')
    owned=load('structured_owned',OWNED);runner_sha=sha(__file__);owned_sha=sha(OWNED)
    OUT.mkdir();src=OUT/'src';src.mkdir();lib=OUT/'lib';lib.mkdir();logs=OUT/'logs';logs.mkdir()
    state={'status':'RUNNING','runner_sha256':runner_sha,'owned_sha256':owned_sha,'initial':initial,'records':[],
           'scope':'Two clients on authenticated fresh base; transitive/dynamic/transient ancestry inherited.'}
    def save():
        p=OUT/'state.tmp';p.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');p.replace(OUT/'state.json')
    save()
    try:
        for source,(name,_,_) in zip(SOURCES,CLIENTS):
            target=src/(name+'.lean');target.write_bytes(source.read_bytes());need(sha(target)==PINS[source] and sha(source)==PINS[source],'client source copy drift')
        env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(driver.BASE_DIR/'lib')+':'+str(driver.PKG),LEAN_NUM_THREADS='1')
        for var in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(var,None)
        tops=ctx['tops']|{n.split('.')[0] for n in ctx['manifest']['external_modules']}
        driver.reject_project_fallbacks((lib,),tops)
        own={}; project=driver.BASE_DIR/'lib'
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
                        'memavailable_bytes':available(),'free_bytes':shutil.disk_usage('/tmp').free}
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
            state['last_process']={'phase':name+' --deps','exit':dcode,'seconds':dseconds,'receipt':dreceipt};save()
            deps_text=depsout.read_text();deps_error=depserr.read_text()
            need(dcode==0 and not deps_error,'client deps failed')
            direct={};input_guards={};counts={}
            for line in deps_text.splitlines():
                path=Path(line);need(path.is_absolute() and path.is_file() and str(path).endswith('.olean'),'invalid client dependency')
                if path.is_relative_to(lib):
                    module=driver.logical_name(path,lib);need(module in own,'unbuilt client dependency');expected_guard=own[module]
                elif path.is_relative_to(project):
                    module=driver.logical_name(path,project)
                    need(module in ctx['manifest']['sources'],('not a base project module',module))
                    expected_guard=ctx['base']['outputs'][module]
                elif path.is_relative_to(driver.PKG) or path.is_relative_to(driver.TOOL):
                    root=driver.PKG if path.is_relative_to(driver.PKG) else driver.TOOL
                    module=driver.logical_name(path,root);expected_guard={k:ctx['base']['guarded_companions'][k] for k in driver.scan(Path(str(path)[:-6]))}
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
            state['last_process']={'phase':name+' compile','exit':code,'seconds':seconds,'receipt':receipt};save()
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
        _,_,after=authenticate();need(after==initial,'authenticated base changed')
        pin();need(sha(__file__)==runner_sha and sha(OWNED)==owned_sha,'runner changed')
        for i,rec in enumerate(state['records']):
            need(sha(SOURCES[i])==PINS[SOURCES[i]] and sha(src/(rec['module']+'.lean'))==PINS[SOURCES[i]],'final client source drift')
            for field in ('log','stderr','deps_stdout','deps_stderr'):need(sha(rec[field])==rec[field+'_sha256'],('log drift',field))
            driver.check_guard(rec['direct_guards']);driver.check_guard(rec['output_guards'])
        driver.check_guard(shadows);driver.reject_project_fallbacks((lib,),tops)
        driver.reject_project_fallbacks((project,driver.PKG,driver.TOOL),{n for n,_,_ in CLIENTS})
        expected_files={p for guard in own.values() for p,entry in guard.items() if entry is not None}
        need(file_inventory(lib)==expected_files,'client output inventory mismatch')
        state.update(status='PASS',phase='complete',samples=[]);save();print('PASS two base-only clients',flush=True)
    except BaseException as exc:
        state.update(status='FAILED',failure=repr(exc));save();raise

def main():
    p=argparse.ArgumentParser();p.add_argument('--run',action='store_true');p.parse_args()
    need(not OUT.exists(),'refusing existing client output')
    driver,ctx,initial=authenticate();need(idle_lean(),'Lean slot busy')
    print(json.dumps({'status':'PREFLIGHT_PASS','initial':initial},sort_keys=True),flush=True)
    if '--run' in sys.argv:run(driver,ctx,initial)
if __name__=='__main__':
    try:main()
    except Exception as exc:print('REFUSED_OR_FAILED',repr(exc),file=sys.stderr);raise SystemExit(1)
