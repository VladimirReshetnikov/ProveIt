#!/usr/bin/env python3
"""Literal internal GIC introduction; exact legacy QuantifierCore parent.
Shared120s, -j1 -M4096, default proof limits, no rebuild/version query/download.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
HERE = Path(__file__).resolve().parent
MODULE = 'ZFCinPA.ValidatorNativeGic254'
SOURCE_SHA = '8e53750fbf17c06f4f5699a19d2c6b2682037f7004bf0d72aa80778c8d2e6680'
AUDIT_SHA = '00259bf811598a193ab4124d2a893c387575e0527ec1526fd8edbe4ed41bf679'
BOUNDARY_SHA = 'bef48d5e15a5f5765364e54d85f719092c895b19be17262263134fb81da3c3fe'
PARENT_SHA = 'a5d44ee88abad04bf5a3a6f6e9a470e2c1b72970cfa5063ea3129dfc300240ca'
PROBES = ['ValidatorNativeGic254.bundleG_eq_internalGic', 'ValidatorNativeGic254.cProv_container', 'ValidatorNativeGic254.cProv_internalGic', 'ValidatorNativeGic254.pad_gt_three', 'ValidatorNativeGic254.pad_equivalent', 'ValidatorNativeGic254.cProv_paddedGic_bounded', 'ValidatorNativeGic254.cProv_paddedGic', 'ValidatorNativeGic254.cProv_closed_paddedGic']
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
    p.add_argument('--source',type=Path,default=HERE/'Lean/ZFCinPA/ValidatorNativeGic254.lean')
    p.add_argument('--audit',type=Path,default=HERE/'validator_native_gic254_audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'results/validator-native-gic254-boundary.json')
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
    require(e['status']=='PASS' and (e['named_axiom_probes'],e['callers'])==(25,18),'Wrong actual parent.')
    require(e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
    for path,h in e['before'].items():pin(path,h)
    for d in b['static_inputs']:pin(d['path'],d['sha256'])
    for k in ['source','audit']:
        pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
    require([q['label'] for q in e['commands']]==['source','audit'],'Wrong parent commands.')
    for c in e['commands']:
        require(c['exit_code']==0 and c['timed_out'] is False,'Parent failed.')
        require('log' not in c and 'interrupted' not in c,'Unexpected historical command schema.')
        pin(Path(b['parent_run'])/(c['label']+'.log'),hashlib.sha256(c['output'].encode()).hexdigest())
    an=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
    rr=reports(e['commands'][1]['output'])
    require(len(an)==25 and [q['name'] for q in rr]==an and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong raw parent reports.')
    require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==18,'Wrong parent typed clients.')
    require(e['warnings']==sum(c['output'].count('warning:') for c in e['commands'])==0,'Parent warnings differ.')
    f,=e['fresh_modules'];pin(f['path'],f['sha256'])
    require(f['module']=='ZFCinPA.ValidatorQuantifierCore254' and f['source_sha256']==e['source']['sha256'] and e['source_passed'] and e['fresh_object_sha256_before_audit']==f['sha256'],'Wrong legacy pre-audit source capture.')
    require('source_pass_object' not in e,'Unexpected legacy schema; do not invent capture fields.')
    pool={q['module']:q for q in e['reused_modules']}
    pool[f['module']]=dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
    reused=b['reused_modules'];providers=b['providers'];tools=b['toolchain_providers']
    require(len(reused)==21 and {q['module']:q for q in reused}==pool,'Wrong exact21-project selection.')
    require(providers==e['providers'] and len(providers)==4 and tools==e['toolchain_providers'],'Wrong cached boundaries.')
    require({q['module'] for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tools.')
    for q in reused+providers:
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
    C=pin(b['compiler']['path'],b['compiler']['sha256']);require(b['compiler']==e['compiler'],'Different compiler.')
    for q in tools:
        pin(q['object'],q['object_sha256']);pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
        require(Path(q['object']).resolve()==(C.parent.parent/'lib/lean'/rel(q['module'])).resolve(),'Wrong toolchain reference.')
    old_roots=[Path(q) for q in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
    for q in reused+providers+tools:
        first_old=next((root/rel(q['module'])).resolve() for root in old_roots if (root/rel(q['module'])).is_file())
        require(first_old==Path(q['object']).resolve(),'Changed historical first provider.')
    require(imports(S)==['ZFCinPA.ValidatorQuantifierCore254'] and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['LeanProofs.ZFCinPA.'+n for n in PROBES] and len(re.findall(r'^example\b',A.read_text(),re.M))==10,'Wrong audit8/10.')
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
    require(seen==set(selected) and found==external,'Wrong project/external DFS.')
    require({q['module'] for q in providers}==external|{'Foundation.FirstOrder.Arithmetic.HFS.Seq'},'Wrong inherited Seq anchor.')
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
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
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
        scope='All-internal literal GIC introduction, double-negation padding and closed domain label. No Foundation GIC encoding identity, full universal closure, proof compiler, reverse consistency or binary endpoint.',
        source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),
        parent_evidence=dict(path=str(E),sha256=PARENT_SHA),parent_scope=b['scope'],compiler=b['compiler'],compiler_version_query_performed=False,
        reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=21,exact_project_import_closure=sorted(seen),
        direct_external_boundaries=sorted(external),inherited_extra_external_modules=['Foundation.FirstOrder.Arithmetic.HFS.Seq'],dependencies=b['dependencies'],
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
        post(); record.update(status='PASS', named_axiom_probes=8, callers=10, axiom_reports=rr, only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True, warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL', error=repr(ex))
        try: post()
        except BaseException as post_error: record['postcheck_error'] = repr(post_error)
        save(); raise
    save(); print(W/'verification.json')

if __name__ == '__main__':
    main()
