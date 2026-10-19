#!/usr/bin/env python3
"""Upstream R2 quantifier rules; four actual parents, exact46 project prerequisites.
Legacy per-command budgets/captures and exact warnings are retained separately.
Shared120s, -j1 -M4096, default proof limits, no rebuild/version query/download.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time
HERE = Path('/tmp/zfc-r2quant')
MODULE = 'ZFCinPA.R2Quant'
SOURCE_SHA = '1220da7c83aa7d86de81805fd26035ffee7bf9c8cc6eef08c98e30a6b6c7e66b'
AUDIT_SHA = '35fba66a917819fee153165b493060932e7487498b77c0b8f6bf09aaf4a3467c'
BOUNDARY_SHA = '234004db1a17a543cbc0b5eac09775adc88062cfc1a09d4b288b62196b6ca45b'
PROBES = ['R2Quant.freeAvoid_even', 'R2Quant.freeAvoid_big', 'R2Quant.freeLabel_lt', 'R2Quant.freeLabel_odd', 'R2Quant.all_iff_of_eqUnder', 'R2Quant.iff2_trans', 'R2Quant.all_step', 'R2Quant.ex_step', 'R2Quant.cProv_gen_ctx', 'R2Quant.all_intro', 'R2Quant.ex_intro']
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
    p.add_argument('--source',type=Path,default=HERE/'R2Quant.lean')
    p.add_argument('--audit',type=Path,default=Path(__file__).resolve().with_name('Audit.lean'))
    p.add_argument('--boundary',type=Path,default=Path(__file__).resolve().with_name('boundary.json'))
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
    b=json.loads(B.read_text());pin(b['template']['path'],b['template']['sha256'])
    pin(b['source_origin']['path'],SOURCE_SHA);require(S.read_bytes()==Path(b['source_origin']['path']).read_bytes(),'Changed upstream source.')
    C=pin(b['compiler']['path'],b['compiler']['sha256']);parent_records={};parent_pools={}
    def pair(q):return {k:q[k] for k in ['module','source','source_sha256','object','object_sha256']}
    for d in b['parents']:
        E=pin(d['path'],d['sha256']);e=json.loads(E.read_text());parent_records[d['key']]=e
        require(e['status']=='PASS' and not e.get('prepare_only',False),'Non-actual parent.')
        require((e['named_axiom_probes'],e['callers'])==(d['probes'],d['callers']),'Wrong parent audit census.')
        require(e['before']==e['after'] and len(e['before'])==d['before_count'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
        require(e['compiler']==b['compiler'] and e['memory_mebibytes']==4096 and e['LEAN_NUM_THREADS']=='1' and e['global_option_overrides']==[],'Wrong parent compiler/options.')
        require(e['compiler_version_query_performed']==d['compiler_version_query_performed'] and not e['dependency_build'] and not e['downloads'],'Wrong parent discovery policy.')
        for k in ['source','audit']:
            require(e[k]==d[k],'Wrong parent source/audit descriptor.');pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
            require([list(x) for x in re.findall(r'^\s*set_option\s+(maxRecDepth|maxHeartbeats)\s+(\S+)',Path(e[k]['snapshot']).read_text(),re.M)]==d['proof_limit_options'][k],'Changed inherited proof limits.')
        f,=e['fresh_modules'];require(f==d['fresh'] and f['module']==d['module'] and f['source_sha256']==e['source']['sha256'],'Wrong parent fresh object.');pin(f['path'],f['sha256'])
        if d['kind']=='modern':
            require(e['shared_timeout_seconds']==120 and not e['compiler_version_query_performed'],'Wrong modern parent budget.')
            require(e['source_object_recorded_before_audit'] and e['source_pass_object']==dict(f,source_command_index=0),'Missing modern pre-audit capture.')
            require(e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'Wrong modern fresh first capture.')
        else:
            require(d['kind']=='legacy' and e['per_command_timeout_seconds']==120 and e['source_passed'] and e['fresh_object_sha256_before_audit']==f['sha256'],'Wrong historical budget/capture.')
            require('actual_first_providers' not in e and 'fresh_first_provider_before_audit' not in e,'Legacy capture schema changed.')
        require([c['label'] for c in e['commands']]==['source','audit'],'Wrong parent commands.')
        parent_snaps=Path(e['audit']['snapshot']).parent
        for c,log in zip(e['commands'],d['logs']):
            require(c['exit_code']==0 and c['timed_out'] is False and c.get('interrupted') is None,'Parent command failed.')
            expected=[str(C)]+(['-j1'] if d['kind']=='modern' else [])+['-M4096','--root='+str(parent_snaps)]+(['-o',f['path']] if c['label']=='source' else [])+[e[c['label']]['snapshot']]
            require(c['command']==expected,'Wrong parent compiler command.');pin(log['path'],log['sha256'])
            require(Path(log['path']).read_text()==c['output'] and 'error:' not in c['output'] and 'sorryAx' not in c['output'],'Wrong raw parent log.')
            if d['kind']=='modern':require(c['log']==log['path'] and c['log_sha256']==log['sha256'],'Wrong modern log capture.')
        rr=reports(e['commands'][1]['output']);names=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
        require(len(names)==d['probes'] and [q['name'] for q in rr]==names and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong parent axiom reports.')
        if d['kind']=='modern':require(rr==e['axiom_reports'],'Wrong modern reports.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==d['callers'],'Wrong parent typed clients.')
        require(e['warnings']==sum(c['output'].count('warning:') for c in e['commands'])==d['warnings'],'Changed parent warnings.')
        require({c['label']:c['output'].count('warning:') for c in e['commands']}==d['warning_counts'],'Wrong warning distribution.')
        require([l for c in e['commands'] for l in c['output'].splitlines() if 'warning:' in l]==d['warning_lines'],'Changed exact warning lines.')
        pool={q['module']:pair(q) for q in e['reused_modules']}
        require(len(pool)==d['project_count'] and sorted(pool)==d['project_modules'],'Wrong pinned parent project set.')
        if d['kind']=='modern':
            require(d['project_closure_schema']=='explicit_list' and isinstance(e['exact_project_import_closure'],list) and len(e['exact_project_import_closure'])==d['project_count'] and set(pool)==set(e['exact_project_import_closure']),'Wrong modern project closure.')
        else:
            require(d['project_closure_schema']=='historical_true' and e['exact_project_import_closure'] is True,'Wrong historical closure attestation.')
        pool[f['module']]=dict(module=f['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],object=f['path'],object_sha256=f['sha256']);parent_pools[d['key']]=pool
        require(e['namespace_overlay']==d['namespace_overlay'] and not e['namespace_overlay']['whole_namespace_independently_attested'],'Wrong inherited overlay scope.')
        require(Path(e['namespace_overlay']['target']).resolve()==Path(e['namespace_overlay']['source']).resolve(),'Changed historical overlay.')
        for name in ['Foundation','Mathlib']:require(e['dependencies'][name]['pin']==b['dependencies'][name]['pin'],'Different dependency revision.')
        require(e['dependencies']['lake_manifest_sha256']==b['dependencies']['lake_manifest_sha256'],'Different dependency manifest.')
    reused=b['reused_modules'];providers=b['providers'];tools=b['toolchain_providers']
    require(len(reused)==46 and len({q['module'] for q in reused})==46 and len(providers)==8 and {q['module'] for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong selected census.')
    for q in reused+providers:
        owner=(b['provider_owners'] if q in reused else b['external_owners'])[q['module']];e=parent_records[owner]
        pool=parent_pools[owner] if q in reused else {x['module']:pair(x) for x in e['providers']}
        require(pool.get(q['module'])==q,'Wrong selected pair ownership.')
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
        fresh=q['module']==e['fresh_modules'][0]['module']
        for k in ['source','object']:
            if k=='object' and fresh:continue
            require(e['before'].get(str(Path(q[k]).resolve()))==q[k+'_sha256'],'Unbound selected parent pair.')
        roots=[Path(x) for x in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
        first_old=next((root/rel(q['module'])).resolve() for root in roots if (root/rel(q['module'])).is_file())
        require(first_old==Path(q['object']).resolve(),'Changed historical first provider.')
        if 'actual_first_providers' in e and not fresh:
            rows={x['module']:x for x in e['actual_first_providers']};require(Path(rows[q['module']]['actual_first']).resolve()==first_old and rows[q['module']]['sha256']==q['object_sha256'],'Wrong modern prior first capture.')
    for q in tools:
        pin(q['object'],q['object_sha256']);pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
        require(Path(q['object']).resolve()==(C.parent.parent/'lib/lean'/rel(q['module'])).resolve(),'Wrong toolchain reference.')
    require(imports(S)==b['direct_imports'] and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['LeanProofs.ZFCinPA.'+n for n in PROBES] and len(re.findall(r'^example\b',A.read_text(),re.M))==14,'Wrong audit11/14.')
    for q in [S,A]:require(not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Untrusted proof shortcut/options.')
    selected={q['module']:q for q in reused};external=set(b['direct_external_boundaries']);seen=set();found=set()
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:return
        if m in external:found.add(m);return
        require(m in selected,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for c in imports(selected[m]['source']):visit(c)
    for m in imports(S):visit(m)
    require(seen==set(selected) and found==external and len(external)==7,'Wrong project/external DFS.')
    require(b['retained_external_boundaries']==['Foundation.FirstOrder.Arithmetic.HFS.Seq'] and {q['module'] for q in providers}==external|set(b['retained_external_boundaries']),'Wrong retained external anchor.')
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
    require(b['libraries']==parent_records['neg']['LEAN_PATH'].split(os.pathsep)[1:] and all(x.is_dir() for x in libs),'Wrong existing library roots.')
    overlay=Path(b['namespace_overlay']['source'])
    require(b['namespace_overlay']==parent_records['neg']['namespace_overlay'] and overlay.is_dir() and b['namespace_overlay']['whole_namespace_independently_attested'] is False,'Wrong inherited namespace overlay.')
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
        scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),
        parent_summaries=b['parents'],legacy_parent_scope=b['legacy_scope'],all_current_parent_inputs_rehashed=False,selected_parent_provider_pairs_rehashed=True,
        compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,
        exact_project_prerequisite_count=46,exact_project_import_closure=sorted(seen),direct_external_boundaries=sorted(external),retained_external_boundaries=b['retained_external_boundaries'],dependencies=b['dependencies'],
        namespace_overlay=dict(target=str(cache/'Foundation'),source=str(overlay.resolve()),whole_namespace_independently_attested=False),before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,
        global_option_overrides=[],source_option_overrides={},audit_option_overrides={},dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
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
        post(); record.update(status='PASS', named_axiom_probes=11, callers=14, axiom_reports=rr, only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True, warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL', error=repr(ex))
        try: post()
        except BaseException as post_error: record['postcheck_error'] = repr(post_error)
        save(); raise
    save(); print(W/'verification.json')

if __name__ == '__main__':
    main()
