#!/usr/bin/env python3
"""Upstream R2 configurable-encoder NNF negation; exact25 actual R2Ctx prerequisites.
Parent keeps one unused-variable warning; the new proof retains IΣ2.
Shared120s, -j1 -M4096, default proof limits, no rebuild/version query/download.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
HERE = Path('/tmp/zfc-r2neg')
MODULE = 'ZFCinPA.R2Neg'
SOURCE_SHA = 'efa03f341e28d45a1fafd8e87d5c1236a06cdae575db2c6604e200f42be9a538'
AUDIT_SHA = '104e932255f82c9f30e339f6a9d92f84e05e16e10cc8b30b32d47a36e7ac68bb'
BOUNDARY_SHA = '761b12eae3be3f9a5901e70039390194fa40ae8dbb8b8d81e659943d393dc35b'
PARENT_SHA = 'a6cd3dbfcc169c5399201d0e8735a3ebfe83891006e09b293bd5ef5acd71bb90'
PROBES = ['R2Neg.taut', 'R2Neg.and_case', 'R2Neg.or_case', 'R2Neg.dneg_right', 'R2Neg.iff2_symm', 'R2Neg.all_iff2', 'R2Neg.neg_swap', 'R2Neg.neg_iff2', 'R2Neg.encode_neg']
STANDARD = {'propext','Classical.choice','Quot.sound'}
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def rel(m,suffix='.olean'): return Path(m.replace('.','/')).with_suffix(suffix)
def imports(p): return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def reports(text):
    rows=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip() for x in a.split(',') if x.strip()})) for n,a in rows]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'R2Neg.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary.json')
    p.add_argument('--parent-evidence',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true')
    args=p.parse_args();require(__debug__,'No optimized Python.')
    S,A,B,W=args.source.resolve(),args.audit.resolve(),args.boundary.resolve(),args.output.resolve()
    require(not W.exists() or (W.is_dir() and not any(W.iterdir())),'Fresh output required.')
    for root in ['/home/codex/.codex/worktrees/ec20/Proofs','/home/codex/src/Proofs']:
        require(not W.is_relative_to(Path(root)),'External output required.')
    tracked={}
    def pin(path,h):
        q=Path(path).resolve();require(q.is_file() and sha(q)==h,'Changed input '+str(q))
        require(str(q) not in tracked or tracked[str(q)]==h,'Conflicting pin.')
        tracked[str(q)]=h;return q
    for q,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(q,h)
    b=json.loads(B.read_text());E=pin(args.parent_evidence or b['parent']['path'],PARENT_SHA)
    require(b['parent']['sha256']==PARENT_SHA,'Wrong parent descriptor.')
    e=json.loads(E.read_text())
    require(e['status']=='PASS' and not e.get('prepare_only',False) and (e['named_axiom_probes'],e['callers'])==(6,10),'Wrong actual parent.')
    require(e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
    require(len(e['before'])==b['parent_before_inputs']==83,'Wrong historical parent input census.')
    # Deliberate selected boundary: never rehash the unrelated full ancestor tree.
    for d in b['static_inputs']:pin(d['path'],d['sha256'])
    require(S.read_bytes()==Path(b['source_origin']['path']).read_bytes(),'Upstream source bytes changed.')
    C=pin(b['compiler']['path'],b['compiler']['sha256']);require(b['compiler']==e['compiler'],'Different compiler.')
    require(e['shared_timeout_seconds']==120 and e['memory_mebibytes']==4096 and e['LEAN_NUM_THREADS']=='1' and e['global_option_overrides']==[],'Wrong parent limits.')
    require(not e['compiler_version_query_performed'] and not e['dependency_build'] and not e['downloads'],'Wrong parent execution boundary.')
    for k in ['source','audit']:
        require(e[k]['sha256']==b['parent_'+k+'_sha256'],'Wrong parent source/audit identity.')
        pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
    require([q['label'] for q in e['commands']]==['source','audit'],'Wrong parent commands.')
    f,=e['fresh_modules'];pin(f['path'],f['sha256'])
    require(f['module']==b['parent_module']=='ZFCinPA.R2Ctx' and f['source_sha256']==e['source']['sha256'] and f['sha256']==b['parent_fresh_object_sha256'],'Wrong parent fresh object.')
    require(e['source_object_recorded_before_audit'] and e['source_pass_object']==dict(f,source_command_index=0),'Missing modern pre-audit capture.')
    require(e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'Wrong modern first-provider capture.')
    parent_snaps=Path(e['audit']['snapshot']).parent
    for c in e['commands']:
        require(c['exit_code']==0 and c['timed_out'] is False and c['interrupted'] is None,'Parent failed.')
        expected=[str(C),'-j1','-M4096','--root='+str(parent_snaps)]+(['-o',f['path']] if c['label']=='source' else [])+[e[c['label']]['snapshot']]
        require(c['command']==expected,'Wrong parent compiler command.')
        pin(c['log'],c['log_sha256']);require(Path(c['log']).read_text()==c['output'] and sha(c['log'])==hashlib.sha256(c['output'].encode()).hexdigest(),'Wrong raw parent log.')
        require('error:' not in c['output'] and 'sorryAx' not in c['output'],'Parent diagnostic.')
    an=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
    rr=reports(e['commands'][1]['output'])
    require(len(an)==6 and [q['name'] for q in rr]==an and rr==e['axiom_reports'] and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong raw parent reports.')
    require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==10,'Wrong parent typed clients.')
    require(e['warnings']==sum(c['output'].count('warning:') for c in e['commands'])==1,'Parent warnings differ.')
    require({c['label']:c['output'].count('warning:') for c in e['commands']}==b['parent_warning_counts']=={'source':1,'audit':0},'Wrong known parent warning census.')
    require([line for c in e['commands'] for line in c['output'].splitlines() if 'warning:' in line]==b['parent_warning_lines'],'Wrong known parent warning.')
    pool={q['module']:q for q in e['reused_modules']}
    require(len(pool)==24 and set(pool)==set(e['exact_project_import_closure']) and e['exact_project_prerequisite_count']==24,'Wrong historical project closure.')
    pool[f['module']]=dict(module=f['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],object=f['path'],object_sha256=f['sha256'])
    reused=b['reused_modules'];providers=b['providers'];tools=b['toolchain_providers']
    require(len(reused)==25 and len({q['module'] for q in reused})==25 and all(pool.get(q['module'])==q for q in reused),'Wrong exact25-project closure.')
    require(sorted(set(pool)-{q['module'] for q in reused})==b['unused_parent_projects'] and b['parent_fresh_module_used'] and f['module'] in {q['module'] for q in reused},'Wrong unused parent boundary.')
    require(providers==e['providers'] and len(providers)==7 and tools==e['toolchain_providers'],'Wrong cached boundaries.')
    require({q['module'] for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tools.')
    for q in reused+providers:
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
    for q in tools:
        pin(q['object'],q['object_sha256']);pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
        require(Path(q['object']).resolve()==(C.parent.parent/'lib/lean'/rel(q['module'])).resolve(),'Wrong toolchain reference.')
    old_roots=[Path(q) for q in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
    old_first={q['module']:q for q in e['actual_first_providers']}
    require(len(old_first)==len(e['actual_first_providers'])==33 and set(old_first)=={q['module'] for q in e['reused_modules']+providers+tools},'Wrong historical first-provider census.')
    for q in reused+providers+tools:
        first_old=next((root/rel(q['module'])).resolve() for root in old_roots if (root/rel(q['module'])).is_file())
        require(first_old==Path(q['object']).resolve(),'Changed selected historical first provider.')
        if q['module']==f['module']:
            require(e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'Wrong parent fresh provider.')
            require(e['before'].get(str(Path(q['source']).resolve()))==q['source_sha256'],'Unbound fresh parent source.')
        else:
            capture=old_first[q['module']]
            require(Path(capture['actual_first']).resolve()==first_old and capture['sha256']==q['object_sha256'],'Wrong recorded historical provider.')
            for k in ['source','object']:
                if k in q:require(e['before'].get(str(Path(q[k]).resolve()))==q[k+'_sha256'],'Unbound historical provider.')
    require(next((root/rel(f['module'])).resolve() for root in old_roots if (root/rel(f['module'])).is_file())==Path(f['path']).resolve(),'Changed parent fresh first provider.')
    require(imports(S)==b['direct_imports'] and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['LeanProofs.ZFCinPA.'+n for n in PROBES] and len(re.findall(r'^example\b',A.read_text(),re.M))==12,'Wrong audit9/12.')
    for q in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Untrusted proof shortcut/options.')
    selected={q['module']:q for q in reused};external=set(b['direct_external_boundaries']);seen=set();found=set()
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:return
        if m in external:found.add(m);return
        require(m in selected,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for c in imports(selected[m]['source']):visit(c)
    for m in imports(S):visit(m)
    require(seen==set(selected) and found==external and len(external)==5,'Wrong project/external DFS.')
    require(b['inherited_extra_external_modules']==['Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1'] and {q['module'] for q in providers}==external|set(b['inherited_extra_external_modules']),'Wrong retained external anchors.')
    require(b['dependencies']==e['dependencies'],'Wrong dependency pins.')
    D=Path(b['dependencies']['root']);pin(D/'lake-manifest.json',b['dependencies']['lake_manifest_sha256'])
    def dependency_state():
        state={}
        for name in ['Foundation','Mathlib']:
            d=b['dependencies'][name];root=Path(d['path'])
            head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip()
            dirty=subprocess.check_output(['git','-C',str(root),'status','--porcelain','--untracked-files=no'],text=True)
            require(head==d['pin'] and d['tracked_clean'] and not dirty,'Changed dependency '+name)
            state[name]=dict(pin=head,tracked_clean=True)
        return state
    dep_state=dependency_state();libs=[Path(x) for x in b['libraries']]
    require(b['libraries']==e['LEAN_PATH'].split(os.pathsep)[1:] and all(x.is_dir() for x in libs),'Wrong existing library roots.')
    overlay=Path(b['namespace_overlay']['source'])
    require(b['namespace_overlay']==e['namespace_overlay'] and overlay.is_dir() and b['namespace_overlay']['whole_namespace_independently_attested'] is False,'Wrong inherited namespace overlay.')
    require(Path(b['namespace_overlay']['target']).resolve()==overlay.resolve(),'Changed historical overlay.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    (cache/'Foundation').symlink_to(overlay.resolve(),target_is_directory=True)
    for q in reused:
        dst=cache/rel(q['module']);dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(Path(q['object']).resolve())
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss)
    aa=snaps/'Audit.lean';shutil.copyfile(A,aa);pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA)
    search=[cache,*libs,C.parent.parent/'lib/lean']
    def first(m):
        q=next((root/rel(m) for root in search if (root/rel(m)).is_file()),None)
        require(q is not None,'Missing provider '+m);return q.resolve()
    def provider_check():
        rows=[]
        for q in reused+providers+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve() and sha(pp)==q['object_sha256'],'Wrong actual first provider '+q['module'])
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=provider_check();env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
    record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,
        scope='Unchanged upstream arbitrary-internal semiformula encoder NNF negation equivalence under IΣ2, with finite propositional helpers under IΣ1. No full R2/R3, native axiom transport, interpreter, binary or PA endpoint check.',
        source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),
        parent_evidence=dict(path=str(E),sha256=PARENT_SHA),parent_scope=b['scope'],inherited_parent_scope=b['inherited_parent_scope'],parent_warning_counts=b['parent_warning_counts'],parent_snapshots=dict(source=e['source'],audit=e['audit']),parent_source_pass_object=e['source_pass_object'],all_current_parent_inputs_rehashed=False,selected_parent_provider_pairs_rehashed=True,historical_parent_before_input_count=len(e['before']),unselected_parent_input_paths_not_rehashed=sorted(set(e['before'])-set(tracked)),compiler=b['compiler'],compiler_version_query_performed=False,
        reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=25,exact_project_import_closure=sorted(seen),
        direct_external_boundaries=sorted(external),inherited_extra_external_modules=b['inherited_extra_external_modules'],dependencies=b['dependencies'],
        namespace_overlay=dict(target=str(cache/'Foundation'),source=str(overlay.resolve()),whole_namespace_independently_attested=False),
        before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,
        global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
    def save():
        (W/'verification.json').write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n')
    def post():
        record['after'] = {q: sha(q) for q in tracked}
        require(record['after'] == record['before'], 'Input changed during check.')
        require(provider_check() == actual and dependency_state() == dep_state, 'Provider/dependency postcheck failed.')
        for q in record['fresh_modules']:
            require(first(q['module']) == Path(q['path']).resolve() and sha(q['path']) == q['sha256'], 'Fresh object/first provider changed.')
        record['all_input_provider_postchecks'] = True
    save()
    try:
        if args.prepare_only:
            post(); save(); print(W/'verification.json'); return
        deadline = time.monotonic() + 120
        def run(label, file, obj=None):
            remaining = deadline-time.monotonic(); require(remaining > 0, 'Shared deadline exhausted.')
            cmd = [str(C), '-j1', '-M4096', '--root='+str(snaps)] + (['-o', str(obj)] if obj else []) + [str(file)]
            started = time.monotonic(); proc = subprocess.Popen(cmd, cwd=snaps, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False; interrupted = None
            try:
                data, _ = proc.communicate(timeout=remaining)
            except BaseException as ex:
                timed_out = isinstance(ex, subprocess.TimeoutExpired); interrupted = None if timed_out else type(ex).__name__
                try: os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                data, _ = proc.communicate()
            out = data.decode(errors='replace'); log = W/(label+'.log'); log.write_text(out)
            record['commands'].append(dict(label=label, command=cmd, seconds=time.monotonic()-started, exit_code=proc.returncode, timed_out=timed_out, interrupted=interrupted, output=out, log=str(log), log_sha256=sha(log)))
            save(); require(not timed_out and interrupted is None and proc.returncode == 0, label+' failed; exact log preserved.')
            require('sorryAx' not in out and "declaration uses 'sorry'" not in out, 'Untrusted declaration in output.')
            return out
        obj = cache/rel(MODULE); require(not obj.exists(), 'Fresh target already present.')
        obj.parent.mkdir(parents=True, exist_ok=True)
        run('source', ss, obj)
        fresh = dict(module=MODULE, path=str(obj), sha256=sha(obj), source_sha256=SOURCE_SHA)
        record['fresh_modules'] = [fresh]
        record['source_pass_object'] = dict(fresh, source_command_index=0)
        require(first(MODULE) == obj.resolve(), 'Fresh source object is not first provider.')
        record['fresh_first_provider_before_audit'] = dict(module=MODULE, path=str(first(MODULE)), sha256=sha(first(MODULE)))
        record['source_object_recorded_before_audit'] = True; save()
        out = run('audit', aa); rr = reports(out)
        require([q['name'] for q in rr] == ['LeanProofs.ZFCinPA.'+n for n in PROBES], 'Wrong ordered actual axiom reports.')
        require(all(set(q['axioms']) <= STANDARD for q in rr), 'Nonstandard axiom report.')
        post(); record.update(status='PASS', named_axiom_probes=9, callers=12, axiom_reports=rr, only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True, warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL', error=repr(ex))
        try: post()
        except BaseException as post_error: record['postcheck_error'] = repr(post_error)
        save(); raise
    save(); print(W/'verification.json')

if __name__ == '__main__':
    main()
