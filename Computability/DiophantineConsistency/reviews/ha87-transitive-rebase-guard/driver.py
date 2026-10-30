#!/usr/bin/env python3
"""Build the exact 87-gate HA endpoint from the current project source DAG.

Project modules are compiled in dependency order; no prebuilt project objects
are inherited. Direct Foundation/Mathlib/Lean package objects remain inherited,
are individually hashed, and their transitive package sources are outside this
receipt. The driver records exact inputs, logs and failure states. `--resume`
requires an unchanged frozen graph. `--rebase` creates a fresh graph and reuses
only verified prior-prefix objects whose source and complete source-declared
transitive project dependency environment still match. The original environment
is reconstructed from surviving origin-overlay objects and verified records;
this cannot rule out unrecorded mutation during the original compilation. A
fully fresh build and independent replay remain stronger obligations.
"""
from __future__ import annotations
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile, time, tomllib
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
TARGET = 'DiophantineConsistency.HAAdaptiveFactor87Checks'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
parser = argparse.ArgumentParser()
parser.add_argument('--resume', type=Path)
parser.add_argument('--rebase', type=Path)
parser.add_argument('--audit-only', action='store_true')
parser.add_argument('--wait-existing-wang', action='store_true',
                    help='wait for an existing ArithmeticWangTable Lean worker; default is to report and compile independently')
args = parser.parse_args()
if args.resume and args.rebase:
    raise SystemExit('choose --resume or --rebase, not both')
root = args.resume.resolve() if args.resume else Path(tempfile.mkdtemp(prefix='ha87-full-transitive-'))
statefile = root / 'state.json'
if args.resume:
    state = json.loads(statefile.read_text())
    state.update(status='RUNNING', phase='resume authentication', failure=None)
else:
    state = {'status':'RUNNING', 'phase':'initialization', 'root':str(root), 'records':[],
             'scope':'Current project sources compiled in dependency order without inherited project objects. Direct external package objects are hashed; their transitive package sources/objects remain inherited. A successful author run is not an independent replay.'}
def save():
    tmp = root / 'state.json.tmp'
    tmp.write_text(json.dumps(state, indent=2, ensure_ascii=False) + '\n')
    tmp.replace(statefile)
def require(path, digest, why):
    if not path.is_file() or sha(path) != digest:
        raise RuntimeError(f'{why} changed or absent: {path}')
class AuditComplete(Exception):
    pass
save(); print('ROOT', root, flush=True)
try:
    cfgpath = ROOT / 'lakefile.toml'
    cfg = tomllib.loads(cfgpath.read_text())
    libs = {x['name']: ROOT / x.get('srcDir', '.') for x in cfg['lean_lib']}
    def uncomment(s):
        out=[]; i=0; depth=0
        while i < len(s):
            if depth:
                if s.startswith('/-',i): depth+=1; i+=2
                elif s.startswith('-/',i): depth-=1; i+=2
                else:
                    if s[i]=='\n': out.append('\n')
                    i+=1
            elif s.startswith('/-',i): depth=1; i+=2
            elif s.startswith('--',i):
                while i<len(s) and s[i]!='\n': i+=1
            else: out.append(s[i]); i+=1
        return ''.join(out)
    sources={}; edges={}; visiting=set(); external=set(); order=[]
    def visit(name):
        if name in sources or name in external: return
        if name in visiting: raise RuntimeError(f'cyclic current-source imports: {name}')
        top=name.split('.')[0]
        if top not in libs:
            external.add(name); return
        f=libs[top] / (name.replace('.','/')+'.lean')
        if not f.is_file():
            if top=='Foundation': external.add(name); return
            raise RuntimeError(f'project source missing: {name} at {f}')
        visiting.add(name); deps=[]
        for line in uncomment(f.read_text()).splitlines():
            m=re.match(r'\s*(?:public\s+)?import\s+(.+)',line)
            if m: deps.extend(m.group(1).split())
        for dep in deps: visit(dep)
        visiting.remove(name);sources[name]=str(f.relative_to(ROOT));edges[name]=deps;order.append(name)
    state['phase']='source graph';save();visit(TARGET)
    if not order or order[-1]!=TARGET: raise RuntimeError('target missing from graph')
    source_hashes={m:sha(ROOT/f) for m,f in sources.items()}
    path_text=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip()
    lean_path=Path(subprocess.check_output(['lake','env','which','lean'],cwd=ROOT,text=True).strip()).resolve()
    prefix=Path(subprocess.check_output([str(lean_path),'--print-prefix'],cwd=ROOT,text=True).strip())
    # The mirror exposes package namespaces only. The historic Foundation
    # provider precedes the canonical package build; neither provider's
    # project namespaces are put in LEAN_PATH.
    historic=Path('/tmp/ha-expression-assembly-vgttkwsl/lib')
    canonical=Path('/home/codex/src/Proofs/.lake/build/lib/lean')
    raw=[Path(x) for x in path_text.split(':') if x]+[prefix/'lib/lean']
    workspace_build=(ROOT/'.lake/build/lib/lean').resolve()
    package_roots=[historic,canonical]+[p for p in raw if p.resolve()!=workspace_build]
    pkg=root/'package-lib';pkg.mkdir(exist_ok=True)
    namespace_dirs={}; top_files={}
    for k,base in enumerate(package_roots):
        if not base.is_dir():continue
        for child in base.iterdir():
            name=child.name
            if k<2 and name!='Foundation':continue
            if child.is_dir():
                if name in libs and name!='Foundation':continue
                namespace_dirs.setdefault(name,[])
                if child.resolve() not in namespace_dirs[name]:namespace_dirs[name].append(child.resolve())
            elif '.olean' in name or name.endswith('.ir'):
                top=name.split('.olean',1)[0] if '.olean' in name else name[:-3]
                if top in libs and top!='Foundation':continue
                top_files.setdefault(name,child.resolve())
    for name,dirs in namespace_dirs.items():
        dest=pkg/name
        if len(dirs)==1:
            if not dest.exists():dest.symlink_to(dirs[0],target_is_directory=True)
        else:
            dest.mkdir(exist_ok=True)
            for provider in dirs:
                for dp,_,fs in os.walk(provider,followlinks=True):
                    for fn in fs:
                        if not ('.olean' in fn or fn.endswith('.ir')):continue
                        f=Path(dp)/fn; q=dest/f.relative_to(provider)
                        q.parent.mkdir(parents=True,exist_ok=True)
                        if not q.exists() and not q.is_symlink():q.symlink_to(f.resolve())
    for name,f in top_files.items():
        q=pkg/name
        if not q.exists() and not q.is_symlink():q.symlink_to(f)
    for name in libs:
        if name!='Foundation' and (pkg/name).exists():
            raise RuntimeError(f'project namespace leaked into package mirror: {name}')
    external_paths={}
    for name in sorted(external):
        hit=pkg/(name.replace('.','/')+'.olean')
        if not hit.is_file():raise RuntimeError(f'external imported object missing from package-only mirror: {name}')
        external_paths[name]=str(hit.resolve())
    external_hashes={m:sha(p) for m,p in external_paths.items()}
    external_companions={}
    for name in sorted(external):
        main=pkg/(name.replace('.','/')+'.olean')
        for q in (Path(str(main)+'.server'),Path(str(main)+'.private'),main.with_suffix('.ir')):
            if q.is_file():external_companions[str(q.relative_to(pkg))]={'path':str(q.resolve()),'sha256':sha(q)}
    anchors={'lakefile':sha(cfgpath),'lean_binary':sha(lean_path),
             'lean_version':subprocess.check_output([str(lean_path),'--version'],text=True).strip()}
    graph={'sources':sources,'edges':edges,'external_paths':external_paths,'order':order,
           'source_hashes':source_hashes,'external_hashes':external_hashes,
           'external_companions':external_companions,'anchors':anchors}
    if args.audit_only:
        state.update(status='AUDIT_PASS', phase='audit-only', graph=graph, module=None)
        save();print('AUDIT_PASS',root,'project_modules',len(order),'direct_external_objects',len(external),flush=True)
        raise AuditComplete
    if args.resume:
        for key in ('sources','edges','external_paths','order','source_hashes','external_hashes','external_companions','anchors'):
            if state['graph'][key]!=graph[key]: raise RuntimeError(f'frozen graph changed: {key}; use --rebase')
    else:
        state['graph']=graph
        snaps=root/'source-snapshots'
        for m,f in sources.items():
            dest=snaps/(m.replace('.','_')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/f,dest);require(dest,source_hashes[m],'source snapshot')
    lib=root/'lib';logs=root/'logs';lib.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
    env=dict(os.environ, LEAN_PATH=str(lib)+':'+str(pkg), LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
    state['LEAN_PATH']=env['LEAN_PATH'];state['package_namespace_providers']={k:[str(p) for p in v] for k,v in namespace_dirs.items()};save()
    prior={}
    if args.rebase:
        old=args.rebase.resolve();prev=json.loads((old/'state.json').read_text())
        if prev['graph']['anchors']!=anchors: raise RuntimeError('rebase compiler or Lake anchors differ')
        prior={r['module']:r for r in prev['records'] if r.get('verified')}
        state['rebase_from']=str(old);state['rebase_state_sha256']=sha(old/'state.json');save()
    prior_state_anchors={}
    def verify_prior_chain(prior_root, module, expected, visited=None):
        # Reused prefix evidence may itself have been reused. Walk the complete
        # chain to an actual successful compiler record, preserving every state,
        # source, object, log and direct dependency digest along the way.
        visited=set() if visited is None else visited
        prior_root=Path(prior_root).resolve();key=(str(prior_root),module)
        if key in visited:raise RuntimeError(f'cyclic rebase provenance: {key}')
        visited.add(key);sp=prior_root/'state.json';prior_state_anchors[str(sp)]=sha(sp)
        st=json.loads(sp.read_text());rows=[r for r in st['records'] if r.get('verified') and r['module']==module]
        if not rows:raise RuntimeError(f'no verified prior record for {module} in {prior_root}')
        rec=rows[-1]
        for field in ('source_sha256','object_sha256','dependency_hashes'):
            if rec[field]!=expected[field]:raise RuntimeError(f'rebase provenance mismatch for {module}: {field}')
        require(prior_root/'lib'/(module.replace('.','/')+'.olean'),rec['object_sha256'],'prior chain object')
        require(prior_root/'logs'/rec['log_file'],rec['log_sha256'],'prior chain log')
        require(prior_root/'source-snapshots'/(module.replace('.','_')+'.lean'),rec['source_sha256'],'prior chain source')
        if rec.get('reused_from'):
            return verify_prior_chain(rec['reused_from'],module,rec,visited)
        elif rec.get('exit')!=0 or not rec.get('command'):
            raise RuntimeError(f'prior chain lacks a successful compiler invocation for {module}')
        return prior_root, rec, st
    # Every file read while authenticating a transitive reuse is rechecked in
    # the final audit. Historical transitive inputs are reconstructed from
    # surviving origin objects, not independently pinned at original compile
    # time. Package-transitive ancestry remains inherited.
    transitive_anchors={}
    def anchored_hash(path):
        path=Path(path); key=str(path)
        if key not in transitive_anchors: transitive_anchors[key]=sha(path)
        return transitive_anchors[key]
    def transitive_environment(origin, original_state, name):
        og=original_state['graph']; oe=og['edges']; osrc=og['sources']
        records={r['module']:r for r in original_state['records'] if r.get('verified')}
        todo=list(edges[name]);seen=set();fingerprints={}
        while todo:
            dep=todo.pop()
            if dep in seen:continue
            seen.add(dep); old_project=dep in osrc; new_project=dep in sources
            if old_project!=new_project:return None, f'project/package classification changed: {dep}'
            if new_project:
                if dep not in oe or oe[dep]!=edges[dep]:return None, f'declared imports changed: {dep}'
                rec=records.get(dep)
                if not rec:return None, f'original verified dependency absent: {dep}'
                old=origin/'lib'/(dep.replace('.','/')+'.olean');cur=lib/(dep.replace('.','/')+'.olean')
                if not old.is_file() or not cur.is_file():return None, f'dependency object absent: {dep}'
                previous=anchored_hash(old);current=anchored_hash(cur)
                if previous!=rec['object_sha256']:raise RuntimeError(f'original transitive object changed: {dep}')
                if previous!=current:return None, f'transitive project object changed: {dep}'
                fingerprints[dep]={'kind':'project','sha256':current,'imports':edges[dep]};todo.extend(edges[dep])
            else:
                if dep not in external_hashes or dep not in og['external_hashes']:return None, f'external dependency absent: {dep}'
                if og['external_hashes'][dep]!=external_hashes[dep]:return None, f'external object changed: {dep}'
                rel=dep.replace('.','/')+'.olean';suffixes=[rel+'.server',rel+'.private',rel[:-len('.olean')]+'.ir'];companions={}
                for relcomp in suffixes:
                    oldc=og['external_companions'].get(relcomp);newc=external_companions.get(relcomp)
                    if bool(oldc)!=bool(newc):return None, f'external companion availability changed: {relcomp}'
                    if oldc and oldc['sha256']!=newc['sha256']:return None, f'external companion changed: {relcomp}'
                    if newc:companions[relcomp]=newc['sha256']
                fingerprints[dep]={'kind':'external','sha256':external_hashes[dep],'companions':companions}
        return fingerprints, None
    completed={r['module']:r for r in state['records'] if r.get('verified')}
    for name in order:
        state['phase']='compile';state['module']=name;save()
        obj=lib/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        deps={}
        for dep in edges[name]:
            if dep in sources:
                q=lib/(dep.replace('.','/')+'.olean')
                if not q.is_file(): raise RuntimeError(f'unbuilt project dependency {dep} for {name}')
            else:q=Path(external_paths[dep])
            deps[dep]=sha(q)
        source=ROOT/sources[name];require(source,source_hashes[name],'source before compile')
        if name in completed:
            rec=completed[name]
            if rec['source_sha256']!=source_hashes[name] or rec['dependency_hashes']!=deps:
                raise RuntimeError(f'completed prefix dependency changed: {name}; use --rebase')
            require(obj,rec['object_sha256'],'completed output');require(logs/rec['log_file'],rec['log_sha256'],'completed log')
            if rec.get('reused_from'):
                if 'original_compile_root' not in rec or 'original_compile_state_sha256' not in rec or 'transitive_manifest' not in rec or 'transitive_manifest_sha256' not in rec:
                    raise RuntimeError(f'completed reused output lacks transitive evidence: {name}')
                origin=Path(rec['original_compile_root']);sp=origin/'state.json'
                require(sp,rec['original_compile_state_sha256'],'completed original compiler state')
                prior_state_anchors[str(sp)]=rec['original_compile_state_sha256']
                manifest=root/'transitive-manifests'/rec['transitive_manifest']
                require(manifest,rec['transitive_manifest_sha256'],'completed transitive manifest')
                fingerprint,reason=transitive_environment(origin,json.loads(sp.read_text()),name)
                if reason or fingerprint!=json.loads(manifest.read_text()):
                    raise RuntimeError(f'completed transitive environment changed: {name}: {reason}')
            continue
        if name in prior:
            oldrec=prior[name]
            if oldrec['source_sha256']==source_hashes[name] and oldrec['dependency_hashes']==deps:
                oldobj=args.rebase.resolve()/'lib'/(name.replace('.','/')+'.olean')
                origin, original_rec, original_state=verify_prior_chain(args.rebase.resolve(),name,oldrec)
                fingerprint,reason=transitive_environment(origin,original_state,name)
                if reason:
                    state.setdefault('transitive_reuse_skips',[]).append({'module':name,'reason':reason,'original_root':str(origin)})
                    save();print(name,'RECOMPILE',reason,flush=True)
                else:
                    require(oldobj,oldrec['object_sha256'],'rebase prior object')
                    require(args.rebase.resolve()/'logs'/oldrec['log_file'],oldrec['log_sha256'],'rebase prior log')
                    require(args.rebase.resolve()/'source-snapshots'/(name.replace('.','_')+'.lean'),oldrec['source_sha256'],'rebase prior source snapshot')
                    if obj.exists() or obj.is_symlink():obj.unlink()
                    obj.symlink_to(oldobj.resolve())
                    log=logs/(name.replace('.','_')+'-reused.log');log.write_text(f"Reused verified author-prefix output from {args.rebase.resolve()}\n")
                    manifest_dir=root/'transitive-manifests';manifest_dir.mkdir(exist_ok=True)
                    manifest=manifest_dir/(name.replace('.','_')+'.json');manifest.write_text(json.dumps(fingerprint,sort_keys=True,indent=2)+'\n')
                    row={'module':name,'source_sha256':source_hashes[name],'dependency_hashes':deps,
                         'object_sha256':sha(obj),'log_sha256':sha(log),'log_file':log.name,
                         'verified':True,'warning_lines':oldrec.get('warning_lines',[]),'axiom_sets':oldrec.get('axiom_sets',[]),
                         'reused_from':str(args.rebase.resolve()),'original_compile_root':str(origin),'original_compile_state_sha256':sha(origin/'state.json'),'transitive_manifest':manifest.name,'transitive_manifest_sha256':sha(manifest)}
                    state['records'].append(row);save();print(name,'REUSED',flush=True);continue
        if name == 'DiophantineConsistency.ArithmeticWangTable':
            def existing_wang():
                lines=subprocess.check_output(['ps','-eo','pid=,args='],text=True).splitlines()
                return [line.strip() for line in lines if re.search(r'(^|\s)\S*/lean\s',line)
                        and str(source) in line]
            workers=existing_wang()
            if workers:
                state['existing_wang_workers']=workers;save()
                print('EXISTING_WANG_WORKERS',workers,flush=True)
                if args.wait_existing_wang:
                    while workers:
                        state['phase']='waiting for existing WangTable worker';state['existing_wang_workers']=workers;save()
                        time.sleep(15);workers=existing_wang()
                    state['phase']='compile';state['existing_wang_workers']=[];save()
        if obj.exists() or obj.is_symlink():obj.unlink()
        attempt=1+sum(r['module']==name for r in state['records'])
        log=logs/(name.replace('.','_')+f'-attempt-{attempt}.log')
        cmd=[str(lean_path),'-M8000','-j1','-DElab.async=false',str(source),'-o',str(obj)]
        t=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(p.stdout)
        warning_lines=[line for line in p.stdout.splitlines() if re.search(r'(^|:)\s*warning:',line)]
        axiom_sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',p.stdout,re.S) if name==TARGET else []
        row={'module':name,'exit':p.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(source),
             'dependency_hashes':deps,'object_sha256':sha(obj) if obj.is_file() else None,
             'log_sha256':sha(log),'log_file':log.name,'command':cmd,'warning_lines':warning_lines,
             'axiom_sets':axiom_sets,'verified':False}
        state['records'].append(row);save()
        if p.returncode or re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b',p.stdout):
            raise RuntimeError(f'compile failed or forbidden diagnostic in {name}: {p.stdout}')
        if name==TARGET:
            if len(axiom_sets)<2:raise RuntimeError('endpoint axiom checks missing')
            for group in axiom_sets:
                extra={x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}
                if extra:raise RuntimeError(f'endpoint contains unapproved axioms: {sorted(extra)}')
        require(source,source_hashes[name],'source after compile')
        for dep,h in deps.items():
            q=lib/(dep.replace('.','/')+'.olean') if dep in sources else Path(external_paths[dep])
            require(q,h,'direct dependency after compile')
        row['verified']=True;save();print(name,'PASS',round(row['seconds'],1),flush=True)
    state['phase']='final authentication';save()
    for m,f in sources.items():
        require(ROOT/f,source_hashes[m],'final current source')
        require(root/'source-snapshots'/(m.replace('.','_')+'.lean'),source_hashes[m],'saved source snapshot')
    for m,p in external_paths.items():require(Path(p),external_hashes[m],'direct package object')
    for rel,row in external_companions.items():
        require(Path(row['path']),row['sha256'],'direct package companion');require(pkg/rel,row['sha256'],'mirrored package companion')
    for rec in state['records']:
        if rec.get('verified'):
            require(lib/(rec['module'].replace('.','/')+'.olean'),rec['object_sha256'],'verified output')
            require(logs/rec['log_file'],rec['log_sha256'],'verified log')
            if rec.get('reused_from'):
                require(root/'transitive-manifests'/rec['transitive_manifest'],rec['transitive_manifest_sha256'],'verified transitive manifest')
    if args.rebase: require(args.rebase.resolve()/'state.json',state['rebase_state_sha256'],'rebase prior state')
    for p,h in prior_state_anchors.items():require(Path(p),h,'rebase ancestor state')
    for p,h in transitive_anchors.items():require(Path(p),h,'transitive reuse object')
    require(cfgpath,anchors['lakefile'],'Lake config');require(lean_path,anchors['lean_binary'],'Lean compiler')
    state.update(status='PASS',phase='complete',module=None);save();print('PASS',root,flush=True)
except AuditComplete:
    pass
except BaseException as exc:
    state.update(status='FAILED',failure={'type':type(exc).__name__,'message':str(exc),
                 'phase':state.get('phase'),'module':state.get('module')});save()
    print('FAILED',root,state['failure'],flush=True);raise
