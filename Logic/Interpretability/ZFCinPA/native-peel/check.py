#!/usr/bin/env python3
"""NativePeel implicit-element repair, exact actual Core plus historical OpenSchema.
Shared120s source/audit, -j1 -M4096, default new proof limits; no rebuild/version.
Historical missing captures/budget fields remain explicit, not reconstructed.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
HERE = Path('/tmp/zfc-native-peel')
MODULE = 'ZFCinPA.NativePeel'
SOURCE_SHA = '737541664f434e4c7e94d947a4d663d2e26b935ed1d920f157747bb00eb25b09'
AUDIT_SHA = 'd2c6a279776041723bc3a5182b265d4fc3c4dfecfd5a16724241c585981ffd9d'
BOUNDARY_SHA = '68640a06b9e8e0f8458a72b6074a26b12886c8fe825d245314e3a204d3c26b4d'
PARENT_RECORDS = [{'path': '/tmp/zfc-internal-interpretation-core-check/run1/verification.json', 'sha256': '3a89f58fd858fe4662c37eb6be85f14685763f02f3cfdc951eecffc103670c8c'}, {'path': '/tmp/zfc-model-coded-closure/open-schema-run4/verification.json', 'sha256': 'fe5abdb0a6be81a729b6b66aba2e3dd061780debe7ab9a7ea3c7cf72b4885002'}]
PROBES = ['NativePeel.derivable_mp', 'NativePeel.domSet_succ_subset', 'NativePeel.shift_qqAlls', 'NativePeel.free_subst_qVec_fvarVec', 'NativePeel.peel_step', 'NativePeel.peel']
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
    p.add_argument('--source',type=Path,default=HERE/'source-v2/NativePeel.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary-v2.json')
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
    b=json.loads(B.read_text())
    require([q['record'] for q in b['parents']]==PARENT_RECORDS,'Wrong actual parent pins.')
    require(b['source']['sha256']==SOURCE_SHA and b['audit']['sha256']==AUDIT_SHA,'Wrong source/audit descriptors.')
    pin(b['source_origin']['path'],b['source_origin']['sha256'])
    for q in b['repair_inputs']:pin(q['path'],q['sha256'])
    require(S.read_text().count('domSet_succ_subset hd hds j hy')==1 and S.read_text().replace('domSet_succ_subset hd hds j hy','domSet_succ_subset hd hds j y hy')==Path(b['source_origin']['path']).read_text(),'Wrong exact one-call repair.')
    C=pin(b['compiler']['path'],b['compiler']['sha256'])
    reused=b['reused_modules'];providers=b['providers'];tools=b['toolchain_providers']
    require((len(reused),len(providers),len(tools))==(13,5,1),'Wrong selected boundary census.')
    require(len({q['module'] for q in reused})==13 and len({q['module'] for q in providers})==5 and {q['module'] for q in tools}=={'Init'},'Duplicate/wrong selected modules.')
    selected_rows={q['module']:q for q in reused+providers+tools}
    paired=set();pool={};summaries=[]
    identity=lambda q:{k:q[k] for k in ['module','source','source_sha256','object','object_sha256']}
    for pd in b['parents']:
        E=pin(pd['record']['path'],pd['record']['sha256']);e=json.loads(E.read_text())
        modern=pd['schema']=='modern'
        require(pd['schema'] in {'modern','legacy'} and e['status']=='PASS' and not e.get('prepare_only',False),'Parent is not actual PASS.')
        require((e['named_axiom_probes'],e['callers'])==(pd['probes'],pd['callers']),'Wrong parent probe/client census.')
        require(e['before']==e['after'] and len(e['before'])==pd['before_count'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
        require(e['compiler']==b['compiler'] and e['dependencies']==b['dependencies'],'Wrong parent compiler/dependencies.')
        require(not e['dependency_build'] and not e['downloads'],'Parent build/download present.')
        require(e['source']==pd['source'] and e['audit']==pd['audit'],'Wrong parent source/audit.')
        for k in ['source','audit']:
            pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
            require(e['before'].get(str(Path(e[k]['path']).resolve()))==e[k]['sha256'],'Unbound parent source/audit.')
        f,=e['fresh_modules'];require(f==pd['fresh'] and f['module']==pd['module'] and f['source_sha256']==e['source']['sha256'],'Wrong parent fresh object.')
        pin(f['path'],f['sha256'])
        require([q['label'] for q in e['commands']]==['source','audit'],'Wrong parent command order.')
        if modern:
            require(pd['name']=='core' and (pd['probes'],pd['callers'],pd['before_count'],pd['project_count'],pd['external_count'],pd['tool_count'])==(7,13,42,3,5,2),'Wrong Core schema.')
            require(e['shared_timeout_seconds']==120 and e['memory_mebibytes']==4096 and e['LEAN_NUM_THREADS']=='1' and e['global_option_overrides']==[] and not e['compiler_version_query_performed'],'Wrong Core execution policy.')
            require(e['source_object_recorded_before_audit'] and e['source_pass_object']==dict(f,source_command_index=0),'Missing Core preaudit capture.')
            require(e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'Wrong Core fresh first capture.')
            require(set(e['exact_project_import_closure'])=={q['module'] for q in e['reused_modules']} and e['exact_project_prerequisite_count']==3,'Wrong Core closure.')
        else:
            require(pd['name']=='schema' and (pd['probes'],pd['callers'],pd['before_count'],pd['project_count'],pd['external_count'],pd['tool_count'])==(11,16,40,9,6,1),'Wrong OpenSchema schema.')
            require(e['exact_project_import_closure'] is True,'Wrong legacy closure flag.')
            require(all(k not in e for k in ['source_pass_object','source_object_recorded_before_audit','fresh_first_provider_before_audit','actual_first_providers','shared_timeout_seconds','memory_mebibytes','LEAN_NUM_THREADS','global_option_overrides','compiler_version_query_performed']),'Unexpected legacy modern evidence.')
        parent_snaps=Path(e['audit']['snapshot']).parent
        for c,log in zip(e['commands'],pd['logs'],strict=True):
            require(c['exit_code']==0,'Parent failed.')
            if modern:require(c['timed_out'] is False and c['interrupted'] is None,'Parent timeout/interruption.')
            else:require(all(k not in c for k in ['timed_out','interrupted','log','log_sha256']),'Changed legacy command schema.')
            expected=[str(C)]+(['-j1'] if modern else [])+['-M4096','--root='+str(parent_snaps)]+(['-o',f['path']] if c['label']=='source' else [])+[e[c['label']]['snapshot']]
            require(c['command']==expected,'Wrong exact parent command.')
            pin(log['path'],log['sha256']);require(Path(log['path']).read_text()==c['output'],'Raw parent log differs.')
            if modern:require(c['log']==log['path'] and c['log_sha256']==log['sha256'],'Wrong recorded modern log.')
            require('error:' not in c['output'] and 'sorryAx' not in c['output'],'Parent diagnostic.')
        an=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(len(an)==pd['probes'] and an==pd['audit_probes'] and [q['name'] for q in rr]==pd['report_names'] and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong exact short-audit/full-report parent names.')
        if modern:require(rr==e['axiom_reports'],'Wrong recorded modern reports.')
        else:require('axiom_reports' not in e,'Unexpected legacy report field.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==pd['callers'],'Wrong typed parent clients.')
        require(e['warnings']==sum(c['output'].count('warning:') for c in e['commands'])==0,'Wrong parent warning census.')
        require((len(e['reused_modules']),len(e['providers']),len(e['toolchain_providers']))==(pd['project_count'],pd['external_count'],pd['tool_count']),'Wrong historical provider census.')
        rows=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],object=f['path'],object_sha256=f['sha256'])]
        for q in rows:
            require(q['module'] not in pool or pool[q['module']]==q,'Conflicting project pair.')
            pool[q['module']]=q
        old_roots=[Path(x) for x in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
        captured={q['module']:q for q in e.get('actual_first_providers',[])}
        if modern:require(len(captured)==len(e['actual_first_providers'])==10,'Wrong modern first-provider count.')
        for q in rows+e['providers']+e['toolchain_providers']:
            if q['module'] not in selected_rows:continue
            expected=selected_rows[q['module']]
            require((identity(q)==identity(expected)) if 'source' in q else q==expected,'Selected pair disagrees with parent.')
            for k in ['source','object']:
                if k in q:
                    pin(q[k],q[k+'_sha256'])
                    if k=='source' or q['module']!=f['module']:
                        require(e['before'].get(str(Path(q[k]).resolve()))==q[k+'_sha256'],'Selected pair unbound by historical inputs.')
            first_old=next((root/rel(q['module'])).resolve() for root in old_roots if (root/rel(q['module'])).is_file())
            require(first_old==Path(q['object']).resolve(),'Changed historical first resolution.')
            if modern and q['module']!=f['module']:
                capture=captured[q['module']];require(Path(capture['actual_first']).resolve()==first_old and capture['sha256']==q['object_sha256'],'Wrong recorded Core first provider.')
            paired.add(q['module'])
        require(e['LEAN_PATH'].split(os.pathsep)[1:]==b['libraries'] and Path(e['namespace_overlay']['source']).resolve()==Path(b['namespace_overlay']['source']).resolve(),'Different inherited namespace/libraries.')
        require(Path(e['namespace_overlay']['target']).resolve()==Path(b['namespace_overlay']['source']).resolve(),'Changed historical overlay.')
        summaries.append(dict(name=pd['name'],record=pd['record'],schema=pd['schema'],fresh=f,probes=pd['probes'],callers=pd['callers'],warnings=0,historical_before_count=len(e['before']),all_historical_inputs_rehashed=False,unselected_historical_paths_not_rehashed=sorted(set(e['before'])-set(tracked))))
    require(paired==set(selected_rows) and set(pool)=={q['module'] for q in reused} and not b['unused_parent_projects'],'Wrong complete selected pair coverage.')
    require(all(pool[q['module']]==q for q in reused),'Wrong selected project pool.')
    require({q['module'] for q in b['canonical_sources']}==set(pool),'Wrong current-source boundary.')
    for q in b['canonical_sources']:
        pin(q['path'],q['sha256']);require(q['sha256']==pool[q['module']]['source_sha256'],'Current source differs from actual parent.')
    for q in tools:
        pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
        require(Path(q['object']).resolve()==(C.parent.parent/'lib/lean'/rel(q['module'])).resolve(),'Wrong exact toolchain provider.')
    require(imports(S)==b['direct_imports'] and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['LeanProofs.ZFCinPA.'+n for n in PROBES] and len(re.findall(r'^example\b',A.read_text(),re.M))==8,'Wrong audit6/8.')
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
    require({q['module'] for q in providers}==external and b['actual_tool_imports']==['Init'],'Wrong exact named external/tool boundary.')
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
    require(overlay.is_dir() and b['namespace_overlay']['whole_namespace_independently_attested'] is False,'Wrong inherited namespace overlay.')
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
        scope=b['scope'],
        source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),
        parent_summaries=summaries,historical_limits=b['historical_limits'],selected_parent_provider_pairs_rehashed=True,all_current_parent_inputs_rehashed=False,compiler=b['compiler'],compiler_version_query_performed=False,
        reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=13,exact_project_import_closure=sorted(seen),
        direct_external_boundaries=sorted(external),actual_tool_imports=b['actual_tool_imports'],dependencies=b['dependencies'],
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
        post(); record.update(status='PASS', named_axiom_probes=6, callers=8, axiom_reports=rr, only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True, warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL', error=repr(ex))
        try: post()
        except BaseException as post_error: record['postcheck_error'] = repr(post_error)
        save(); raise
    save(); print(W/'verification.json')

if __name__ == '__main__':
    main()
