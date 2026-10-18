#!/usr/bin/env python3
"""Check only the logical seed adapter and its audit, using existing exact providers."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
BINDINGS_SHA='45bb30063fd7cb35885944620bcfc1e6dfcb64c34ebed01df20ccabaf3b15c7a'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,msg):
    if not b: raise RuntimeError(msg)
def imports(p):return re.findall(r'^import\s+(\S+)\s*$',p.read_text(),re.M)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/LogicalSeed246.lean')
    ap.add_argument('--audit',type=Path,default=HERE/'logical_seed246_audit.lean')
    ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args()
    W=a.output.resolve();need(not W.is_relative_to(REPO) and (not W.exists()or not any(W.iterdir())),'Fresh external output required.')
    B=HERE/'results/prefix246-logical-seed-bindings.json';need(sha(B)==BINDINGS_SHA,'Bindings changed.');cfg=json.loads(B.read_text())
    S=a.source.resolve();A=a.audit.resolve();E=Path(cfg['evidence']['path']);C=Path(cfg['compiler']['path'])
    for p,h in [(S,cfg['source_sha256']),(A,cfg['audit_sha256']),(E,cfg['evidence']['sha256']),(C,cfg['compiler']['sha256'])]:need(sha(p)==h,'Input changed: '+str(p))
    prior=json.loads(E.read_text())
    need(prior['status']=='PASS167-unit source-verified integration' and prior['only_standard_axioms'] and prior['all_source_identities_unchanged_after_check'] and prior['all_reused_object_identities_unchanged_after_check'],'Incomplete integration evidence.')
    need(prior['compiler']=={k:v for k,v in cfg['compiler'].items()if k!='sha256'},'Compiler boundary changed.')
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',S.read_text()),'Proof shortcut.')
    need(not re.search(r'set_option\s+max(Heartbeats|RecDepth)',S.read_text()+A.read_text()),'Keep default limits.')
    need(imports(A)==[cfg['module']],'Audit imports changed.')
    need(re.findall(r'^#print axioms (.+)$',A.read_text(),re.M)==cfg['probes'] and len(re.findall(r'^example\b',A.read_text(),re.M))==cfg['callers'],'Audit contract changed.')
    pool={q['module']:q for q in cfg['providers']};seen=set();visiting=set();tc={'Init'}
    old={str((REPO/q['path']).resolve()):q for q in prior['source_closure']}
    def visit(m):
        if m in seen:return
        need(m in pool and m not in visiting,'Unknown/cyclic project import '+m);visiting.add(m);q=pool[m]
        src=Path(q['source']);obj=Path(q['object']);o=old[str(src)]
        need(sha(src)==q['source_sha256']==o['sha256'] and sha(obj)==q['object_sha256']==o['olean_sha256'],'Provider changed: '+m)
        need(Path(o['olean']).resolve()==obj.resolve(),'Selected object differs: '+m)
        for c in imports(src):
            if c=='Init'or c.startswith(('Lean.','Std.')):tc.add(c)
            else:visit(c)
        visiting.remove(m);seen.add(m)
    for m in imports(S):visit(m)
    need(seen==set(pool) and len(pool)==94,'Provider closure differs.')
    need(tc=={q['module']for q in cfg['toolchain_providers']}=={'Init'},'Toolchain imports changed.')
    for q in cfg['toolchain_providers']:
        need(sha(q['object'])==q['object_sha256'],'Toolchain provider changed.')
        need(Path(q['object']).resolve()==(C.parent.parent/'lib/lean'/Path(q['module'].replace('.','/')).with_suffix('.olean')).resolve(),'Toolchain path differs.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';actual=[]
    for q in pool.values():
        p=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(q['object'])
        actual.append(dict(module=q['module'],actual_first=str(p),resolved=str(p.resolve()),sha256=sha(p)))
    snap=W/'sources'/Path(cfg['module'].replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True)
    aud=W/'Audit.lean';shutil.copyfile(S,snap);shutil.copyfile(A,aud)
    files=list(dict.fromkeys([Path(__file__).resolve(),B,S,A,E,C,snap,aud]+[Path(q[k])for q in pool.values()for k in ['source','object']]+[Path(q['object'])for q in cfg['toolchain_providers']]))
    before={str(p):sha(p)for p in files}
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Exact logical seed only; no binary run, blank initialization or PA-internal theorem.',source=dict(path=str(S),sha256=sha(S),snapshot=str(snap)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aud)),compiler=cfg['compiler'],compiler_version_query_performed=False,provider_evidence=[cfg['evidence']],reused_modules=list(pool.values()),toolchain_providers=cfg['toolchain_providers'],actual_first_providers=actual,exact_project_import_closure=True,project_module_count=94,commands=[],fresh_modules=[],before=before,LEAN_PATH=str(cache),dependency_build=False,downloads=False,limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'))
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        r['after']={str(p):sha(p)for p in files};need(r['after']==before,'Input/provider changed during run.')
        for q in actual:need(Path(q['actual_first']).resolve()==Path(q['resolved']) and sha(q['actual_first'])==q['sha256'],'First provider changed.')
        r['all_input_provider_postchecks']=True
    save()
    if a.prepare_only:post();save();print(W/'verification.json');return
    env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1');deadline=time.monotonic()+120
    def run(label,args):
        began=time.monotonic();remaining=deadline-began;need(remaining>0,'Shared budget exhausted.')
        try:
            p=subprocess.run([str(C),'-j1','-M4096',*args],cwd=W,env=env,text=True,capture_output=True,timeout=remaining)
            output=p.stdout+p.stderr;code=p.returncode
        except subprocess.TimeoutExpired as ex:
            dec=lambda x:x.decode(errors='replace')if isinstance(x,bytes)else(x or'')
            output=dec(ex.stdout)+dec(ex.stderr)+'\nTIMEOUT\n';code=-1
        (W/(label+'.log')).write_text(output)
        r['commands'].append(dict(label=label,command=[str(C),'-j1','-M4096',*args],seconds=time.monotonic()-began,exit_code=code,output=output));save()
        need(code==0 and 'sorryAx'not in output and "declaration uses 'sorry'"not in output,label+' failed.');return output
    try:
        obj=cache/Path(cfg['module'].replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        so=run('source',['--root='+str(W/'sources'),'-o',str(obj),str(snap)])
        need(obj.is_file()and not obj.is_symlink(),'Missing fresh object.')
        fresh=dict(module=cfg['module'],path=str(obj),sha256=sha(obj),source_sha256=sha(snap))
        r.update(fresh_modules=[fresh],source_pass_object=fresh,source_object_recorded_before_audit=True);save()
        ao=run('audit',[str(aud)])
        reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",ao,re.S)
        need([n for n,b in reports]==cfg['probes'],'Missing/reordered probes.')
        ax=[dict(name=n,axioms=[x.strip()for x in b.split(',')if x.strip()])for n,b in reports]
        need(all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'}for q in ax),'Unexpected axioms.')
        need(sha(obj)==fresh['sha256'],'Object changed during audit.');post()
        r.update(status='PASS',actual_axiom_sets=ax,named_axiom_probes=len(ax),callers=cfg['callers'],only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=dict(source=so.count('warning:'),audit=ao.count('warning:')))
    except Exception as ex:
        r.update(status='FAIL',error=str(ex))
        try:post()
        except Exception as e:r['postcheck_error']=str(e)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
