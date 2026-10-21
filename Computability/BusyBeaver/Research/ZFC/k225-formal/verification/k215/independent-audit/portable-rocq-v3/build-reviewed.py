#!/usr/bin/env python3
"""Serial, resumable endpoint build. Exact pinned reference sources; editable K215 sources.
The dependency scanner selects source dependencies only; Rocq itself resolves/checks imports.
All compiler invocations share the machine-wide Lean/Rocq lock. No axioms or admit flags.
"""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,re,shutil,signal,subprocess,time
EXT=Path(__file__).resolve().parents[3]/'rocq'/'rocq-extension'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x): Path(p).write_text(json.dumps(x,indent=2)+'\n')
def uncomment(s):
    out=[]; d=0; i=0
    while i<len(s):
        if s[i:i+2]=='(*': d+=1;i+=2
        elif s[i:i+2]=='*)' and d: d-=1;i+=2
        else:
            if not d: out.append(s[i])
            i+=1
    assert d==0
    return ''.join(out)
def endpoint_gate(name,output):
    return name not in ('K215F.Correct215','K215F.CorrectDense215') or (
        output.count('Closed under the global context')==2 and 'Axioms:' not in output)
def reusable(old,inputs,obj):
    if not (old.get('status')=='PASS' and old.get('exit_code')==0
            and old.get('post_inputs_unchanged') is True and old.get('inputs')==inputs
            and obj.exists() and sha(obj)==old.get('object_sha256')):
        return False
    log=Path(old['source_snapshot']).parent/'output.log'
    return (log.is_file() and sha(log)==old.get('output_sha256')
            and endpoint_gate(old['module'],log.read_text()))
def bind_toolchain(path,current):
    if path.exists():
        assert json.loads(path.read_text())==current,'Toolchain changed: use a fresh output directory'
    else:write(path,current)
def stop_signal(signum,frame):
    raise KeyboardInterrupt('Build terminated by signal '+str(signum))
def proof_process(cmd,env,cwd,log):
    proc=None
    try:
        # Block interruption only during spawn; the outer handler owns the child
        # before pending SIGINT/SIGTERM is delivered on restoring the mask.
        oldmask=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGINT,signal.SIGTERM})
        try:
            proc=subprocess.Popen(cmd,env=env,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,
                                  preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK,oldmask))
        finally:signal.pthread_sigmask(signal.SIG_SETMASK,oldmask)
        proc.wait()
    except BaseException:
        if proc is not None:
            try:os.killpg(proc.pid,signal.SIGTERM)
            except ProcessLookupError:pass
            try:proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL);proc.wait()
        raise
    return proc
def main():
    global ROOT,REF,JEFF,WORK,COQC
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--reference',type=Path,required=True,help='Exact pinned k230-rocq checkout')
    ap.add_argument('--jeff-reference',type=Path,required=True,help='Exact pinned busy-beaver checkout')
    ap.add_argument('--output',type=Path,required=True,help='Private build and receipt directory')
    ap.add_argument('--switch',default='proofs-rocq91',help='opam switch with Rocq9.1.0 and stdlib9.0.0')
    ap.add_argument('--lock-file',type=Path,default=Path('/tmp/proveit-k215-proof-build.lock'))
    ap.add_argument('--plan-only',action='store_true')
    ap.add_argument('--kernel',action='store_true',help='Also recursively recheck the complete dense endpoint with coqchk')
    a=ap.parse_args()
    signal.signal(signal.SIGTERM,stop_signal)
    ROOT=a.output.resolve();ROOT.mkdir(parents=True,exist_ok=True)
    REF=a.reference.resolve();JEFF=a.jeff_reference.resolve()
    WORK=ROOT/'work';WORK.mkdir(exist_ok=True)
    rm=json.loads((REF/'manifest.json').read_bytes()); em=json.loads((EXT/'manifest.json').read_bytes())
    assert sha(REF/'manifest.json')==em['reference_manifest_sha256']
    roots={n:WORK/n for n in rm['logical_roots']}; roots['K215F']=WORK/'K215F'
    for p in roots.values(): p.mkdir(parents=True,exist_ok=True)
    modules={}
    for rel in rm['compile_order']:
        if rel in rm['reference_files']:
            v=rm['reference_files'][rel]; src=JEFF/v['source'];expected=v['sha256']
        else: src=REF/rel;expected=rm['local_files'][rel]
        assert sha(src)==expected,src
        options=[(n,r) for n,r in rm['logical_roots'].items() if rel.startswith(r+'/')]
        assert len(options)==1,(rel,options)
        n,r=options[0]; suffix=rel[len(r)+1:]; name=n+'.'+suffix[:-2].replace('/','.')
        modules[name]={'source':str(src),'target':str(roots[n]/suffix),'expected_reference_sha256':expected}
    for name in em['variants']['215']['compile_order']:
        modules['K215F.'+name]={'source':str(EXT/'coq/215'/f'{name}.v'),'target':str(roots['K215F']/f'{name}.v')}
    for name,m in modules.items():
        s=uncomment(Path(m['source']).read_text()); deps=[]
        for match in re.finditer(r'(?:From\s+([\w.]+)\s+)?Require\s+(?:(?:Import|Export)\s+)?([\w.\s]+?)\.(?=\s|$)',s):
            prefix,terms=match.groups()
            for term in terms.split():
                q=(prefix+'.' if prefix else '')+term
                if q.startswith('Coq.'): q='Stdlib.'+q[4:]
                if q in modules: deps.append(q)
                elif prefix is not None and q.split('.')[0] not in ('Coq','Stdlib'):
                    hits=[x for x in modules if x.startswith(prefix+'.') and x.endswith('.'+term)]
                    if len(hits)==1:deps.append(hits[0])
                    else:raise RuntimeError((name,'unresolved/ambiguous',q,hits))
                elif prefix is None:
                    hits=[x for x in modules if x.endswith('.'+q)]
                    if len(hits)==1: deps.append(hits[0])
                    elif hits: raise RuntimeError((name,'ambiguous unqualified import',q,hits))
        m['dependencies']=list(dict.fromkeys(deps))
    order=[];active=set();seen=set()
    def visit(n):
        assert n not in active,n
        if n in seen:return
        active.add(n)
        for d in modules[n]['dependencies']:visit(d)
        active.remove(n);seen.add(n);order.append(n)
    for target in ('K215F.EnumPerm','K215F.L1_CompPerm','K215F.L1_SoundPerm','K215F.SeedPerm','K215F.L2RootPerm','K215F.Dense215','K215F.Sim230Main','K215F.Source215','K215F.CorrectDense215'):
        visit(target)
    flags=[]
    for n,p in roots.items():flags+=['-Q',str(p),n]
    plan={'target':'K215F.CorrectDense215','order':order,'count':len(order),'reference_count':sum(not n.startswith('K215F.') for n in order),'flags':flags,'modules':{n:modules[n] for n in order},'reference_manifest_sha256':sha(REF/'manifest.json')}
    write(ROOT/'plan.json',plan)
    print('PLAN',plan['count'],'modules',plan['reference_count'],'reference',flush=True)
    if a.plan_only:return
    env=json.loads(subprocess.check_output(['opam','exec','--switch='+a.switch,'--','python3','-c','import os,json; print(json.dumps(dict(os.environ)))'],text=True))
    compiler=shutil.which('coqc',path=env['PATH']);assert compiler,'coqc not found in selected switch'
    COQC=Path(compiler)
    version=subprocess.check_output([str(COQC),'--version'],env=env,text=True).strip()
    assert 'version 9.1.0' in version,version
    stdlib=subprocess.check_output(['opam','list','--switch='+a.switch,'--installed','--short','--columns=version','--color=never','rocq-stdlib'],text=True).strip();assert stdlib=='9.0.0',stdlib
    prefix=Path(env['OPAM_SWITCH_PREFIX']).resolve()
    installed=prefix/'lib/coq'
    library={str(p.relative_to(installed)):sha(p) for p in sorted(installed.rglob('*.vo'))}
    assert library,'No installed Rocq library objects'
    toolchain={'compiler':version,'stdlib':stdlib,'switch_prefix':str(prefix),
               'coqc_sha256':sha(COQC),'coqchk_sha256':sha(COQC.with_name('coqchk')),
               'rocqworker_sha256':sha(prefix/'lib/rocq-runtime/rocqworker'),
               'installed_library_objects':library}
    bind_toolchain(ROOT/'toolchain.json',toolchain)
    toolchain_sha256=sha(ROOT/'toolchain.json')
    records=ROOT/'records';records.mkdir(exist_ok=True);attempts=ROOT/'attempts';attempts.mkdir(exist_ok=True)
    for idx,name in enumerate(order):
        m=modules[name];src=Path(m['source']);dst=Path(m['target']);dst.parent.mkdir(parents=True,exist_ok=True)
        inputs={str(src):sha(src)}
        for dep in m['dependencies']:
            obj=Path(modules[dep]['target']).with_suffix('.vo');inputs[str(obj)]=sha(obj)
        record=records/(name+'.json');obj=dst.with_suffix('.vo')
        if record.exists():
            old=json.loads(record.read_bytes())
            if old.get('toolchain_sha256')==toolchain_sha256 and reusable(old,inputs,obj):
                print('REUSE',idx+1,name,flush=True);continue
        shutil.copyfile(src,dst)
        base=attempts/name;base.mkdir(exist_ok=True);number=len(list(base.glob('run*')))+1;run=base/f'run{number}';run.mkdir()
        shutil.copyfile(src,run/src.name)
        opts=['-w','-deprecated,-notation-overridden']
        if name.startswith('Undecidability.'):opts+=['-set','Default Proof Using = Type']
        cmd=[str(COQC),*flags,*opts,str(dst)]
        item={'module':name,'argv':cmd,'inputs':inputs,'toolchain_sha256':toolchain_sha256,'source_sha256':sha(src),'source_snapshot':str(run/src.name),'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'status':'WAITING_LOCK'}
        write(run/'record.json',item);print('WAIT',idx+1,name,flush=True)
        with a.lock_file.open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX); t=time.monotonic(); print('START',idx+1,name,flush=True)
            with (run/'output.log').open('w') as log:
                proc=proof_process(cmd,env,WORK,log)
            item.update(exit_code=proc.returncode,seconds=time.monotonic()-t,status='PASS' if proc.returncode==0 else 'FAIL')
        item['post_inputs_unchanged']=all(Path(p).exists() and sha(p)==h for p,h in inputs.items());assert item['post_inputs_unchanged']
        output=(run/'output.log').read_text();item['output_sha256']=sha(run/'output.log');item['closed_reports']=output.count('Closed under the global context')
        item['assumption_gate_passed']=endpoint_gate(name,output)
        if proc.returncode==0 and not item['assumption_gate_passed']:item['status']='FAIL_ASSUMPTIONS'
        if proc.returncode==0:item['object_sha256']=sha(obj)
        write(run/'record.json',item);write(record,item)
        print(item['status'],name,round(item['seconds'],3),flush=True)
        if proc.returncode: print(output[-12000:],flush=True);raise SystemExit(proc.returncode)
        assert item['assumption_gate_passed'],output
        time.sleep(.3)
    if a.kernel:
        base=ROOT/'kernel';base.mkdir(exist_ok=True);run=base/('run'+str(len(list(base.glob('run*')))+1));run.mkdir()
        cmd=[str(COQC.with_name('coqchk')),*flags,'-silent','-o','K215F.CorrectDense215']
        inputs={str(Path(modules[n]['target']).with_suffix('.vo')):sha(Path(modules[n]['target']).with_suffix('.vo')) for n in order}
        item={'argv':cmd,'inputs':inputs,'toolchain_sha256':toolchain_sha256,'status':'WAITING_LOCK'};write(run/'record.json',item);print('WAIT coqchk',flush=True)
        with a.lock_file.open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX);t=time.monotonic();print('START coqchk',flush=True)
            with (run/'output.log').open('w') as log:proc=proof_process(cmd,env,WORK,log)
        item.update(exit_code=proc.returncode,seconds=time.monotonic()-t,status='PASS' if proc.returncode==0 else 'FAIL',output_sha256=sha(run/'output.log'),post_inputs_unchanged=all(sha(p)==h for p,h in inputs.items()))
        write(run/'record.json',item);print('KERNEL',item['status'],flush=True);assert proc.returncode==0 and item['post_inputs_unchanged']
if __name__=='__main__':main()
