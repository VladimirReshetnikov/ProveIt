#!/usr/bin/env python3
"""Native GIC ordered slots/parity vacancy: four actual parents, exact selected closure.
Shared120s, -j1 -M4096, default proof limits; no version query/build/download.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE = Path(__file__).resolve().parent
MODULE = 'ZFCinPA.ValidatorNativeGicSlots254'
SOURCE_SHA = '48b38859d5963c6046963c6af1a24dd0bd4988a3a819a94cfcf0175fd35ffae6'
AUDIT_SHA = 'e8b3e8a3e16eb70ed5ba0bfee21b740a928218bec3af4994ff9ef5562a7d7686'
BOUNDARY_SHA = 'a5eb87f687e1e604cec72dc020abfe1494984d122af9b6a2dac3be86d48ba040'
PROBES = ['ValidatorNativeGicSlots254.encode_gic_support_slots', 'ValidatorNativeGicSlots254.encode_gic_coverage_slots', 'ValidatorNativeGicSlots254.pad_even', 'ValidatorNativeGicSlots254.even_avoids_odd_env', 'ValidatorNativeGicSlots254.even_free_avoids_odd_env', 'ValidatorNativeGicSlots254.even_stream_avoid', 'ValidatorNativeGicSlots254.padded_matrix_resources', 'ValidatorNativeGicSlots254.cProv_paddedGic_odd']
STANDARD = {'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(x,msg):
    if not x:raise RuntimeError(msg)
def rel(m,suffix='.olean'):return Path(m.replace('.','/')).with_suffix(suffix)
def imports(p):return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def reports(text):
    rows=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip() for x in a.split(',') if x.strip()})) for n,a in rows]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'Lean/ZFCinPA/ValidatorNativeGicSlots254.lean')
    p.add_argument('--audit',type=Path,default=HERE/'validator_native_gic_slots254_audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'results/validator-native-gic-slots254-boundary.json')
    for name in ['substitution','native','literal','vacuity']:p.add_argument('--'+name+'-evidence',type=Path)
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
        require(str(q) not in tracked or tracked[str(q)]==h,'Conflicting input identity.');tracked[str(q)]=h;return q
    for q,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(q,h)
    b=json.loads(B.read_text());C=pin(b['compiler']['path'],b['compiler']['sha256'])
    require(set(b['parents'])=={'substitution','native','literal','vacuity'},'Wrong parent set.')
    pool={};external_pool={};tool_pool={};summaries={};snapshots=[]
    def add(pool,row):
        fields=['module','source','source_sha256','object','object_sha256'] if 'source' in row else ['module','object','object_sha256']
        item={k:row[k] for k in fields}
        for k in ['source','object']:
            if k in item:pin(item[k],item[k+'_sha256'])
        if item['module'] in pool:
            old=pool[item['module']]
            require(old['object_sha256']==item['object_sha256'] and Path(old['object']).resolve()==Path(item['object']).resolve(),'Conflicting object provider.')
            if 'source' in item:require(old['source_sha256']==item['source_sha256'],'Conflicting source provider.')
        else:pool[item['module']]=item
    for name,spec in b['parents'].items():
        E=pin(getattr(args,name+'_evidence') or spec['record']['path'],spec['record']['sha256']);e=json.loads(E.read_text())
        require(e['status']=='PASS' and not e.get('prepare_only',False) and (e['named_axiom_probes'],e['callers'])==(spec['probes'],spec['callers']),'Wrong parent outcome.')
        require(e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
        require(len(e['before'])==spec['before_inputs'],'Changed parent census.')
        for path,h in e['before'].items():pin(path,h)
        require(e['compiler']==b['compiler'] and e['dependencies']==b['dependencies'],'Compiler/dependency mismatch.')
        require((e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(4096,'1',[]) and not e['dependency_build'] and not e['downloads'],'Wrong parent resource boundary.')
        legacy=spec['schema']=='legacy_vacuity';require(legacy==(name=='vacuity'),'Wrong legacy schema.')
        if legacy:
            require(e['per_command_timeout_seconds']==120 and e['compiler_version_query_performed'] is True and 'shared_timeout_seconds' not in e and 'actual_first_providers' not in e,'Wrong legacy limits/capture boundary.')
        else:require(e['shared_timeout_seconds']==120 and not e['compiler_version_query_performed'],'Wrong modern limits.')
        for role in ['source','audit']:
            require(e[role]['sha256']==spec[role+'_sha256'],'Wrong parent source/audit.')
            for key in ['path','snapshot']:pin(e[role][key],e[role]['sha256'])
        require([q['label'] for q in e['commands']]==['source','audit'],'Wrong parent commands.')
        for c in e['commands']:
            require(c['exit_code']==0 and not c['timed_out'] and c.get('interrupted') is None,'Parent command failed.')
            prefix=[str(C),'-M4096'] if legacy else [str(C),'-j1','-M4096']
            require(c['command'][:len(prefix)]==prefix and c['command'][-1]==e[c['label']]['snapshot'],'Wrong parent argv.')
            require(len(c['command'])==len(prefix)+(4 if c['label']=='source' else 2) and c['command'][len(prefix)].startswith('--root='),'Extra parent compiler options.')
            if legacy:require('log' not in c and 'interrupted' not in c,'Unexpected legacy command schema.')
            log=Path(c['log']) if not legacy else Path(spec['run'])/(c['label']+'.log')
            pin(log,hashlib.sha256(c['output'].encode()).hexdigest());require(log.read_text()==c['output'],'Changed raw parent log.')
            if not legacy:require(c['log_sha256']==sha(log),'Wrong raw log hash.')
            require('error:' not in c['output'] and 'sorryAx' not in c['output'],'Parent diagnostic.')
        require(e['warnings']==spec['warnings']==sum(c['output'].count('warning:') for c in e['commands']),'Wrong historical warnings.')
        require(e['warnings']==(2 if legacy else 0),'Wrong expected warning policy.')
        names=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(len(names)==spec['probes'] and [q['name'] for q in rr]==names and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong parent axiom reports.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==spec['callers'],'Wrong parent caller census.')
        f,=e['fresh_modules'];pin(f['path'],f['sha256'])
        require(f['module']==spec['module'] and f['source_sha256']==e['source']['sha256'] and f['sha256']==spec['fresh_object_sha256'],'Wrong parent fresh object.')
        if legacy:
            require(e['source_passed'] and e['fresh_object_sha256_before_audit']==f['sha256'] and 'source_pass_object' not in e,'Wrong legacy source capture.')
        else:
            require(e['source_pass_object']==dict(f,source_command_index=0) and e['source_object_recorded_before_audit'],'Wrong modern source capture.')
            require(e['fresh_first_provider_before_audit']=={k:f[k] for k in ['module','path','sha256']},'Wrong modern first capture.')
        roots=[Path(x) for x in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
        def parent_first(m):return next((root/rel(m)).resolve() for root in roots if (root/rel(m)).is_file())
        require(parent_first(f['module'])==Path(f['path']).resolve(),'Fresh parent is not first.')
        first={q['module']:q for q in e.get('actual_first_providers',[])}
        for row in e['reused_modules']+e['providers']+e['toolchain_providers']:
            for k in ['source','object']:
                if k in row:
                    pp=pin(row[k],row[k+'_sha256']);require(e['before'].get(str(pp))==row[k+'_sha256'],'Unbound historical pair.')
            require(parent_first(row['module'])==Path(row['object']).resolve(),'Wrong current parent first provider.')
            if not legacy:
                v=first[row['module']];require(Path(v['actual_first']).resolve()==Path(row['object']).resolve() and v['sha256']==row['object_sha256'],'Wrong recorded parent first provider.')
        for row in e['reused_modules']:add(pool,row)
        add(pool,dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256']))
        for row in e['providers']:add(external_pool,row)
        for row in e['toolchain_providers']:
            add(tool_pool,row);pin(row['toolchain_reference'],row['toolchain_reference_sha256'])
            require(Path(row['object']).resolve()==(C.parent.parent/'lib/lean'/rel(row['module'])).resolve(),'Wrong toolchain boundary.')
        require(e['LEAN_PATH'].split(os.pathsep)[1:]==b['libraries'],'Different retained libraries.')
        if 'namespace_overlay' in e:
            ov=e['namespace_overlay'];require(ov['source']==b['namespace_overlay']['source'] and ov['whole_namespace_independently_attested'] is False and Path(ov['target']).resolve()==Path(ov['source']).resolve(),'Wrong historical namespace overlay.')
        summaries[name]=dict(verification=dict(path=str(E),sha256=spec['record']['sha256']),schema=spec['schema'],warnings=e['warnings'],modern_capture=not legacy,all_current_parent_inputs_rehashed=True,fresh_module=f)
        snapshots.append(dict(source=e['source'],audit=e['audit']))
    reused=b['reused_modules'];providers=b['providers'];tools=b['toolchain_providers']
    def core(row):return {k:row[k] for k in ['module','source','source_sha256','object','object_sha256']}
    require({q['module']:core(q) for q in reused}==pool and len(reused)==31,'Wrong exact31-project union.')
    require({q['module']:core(q) for q in providers}==external_pool and len(providers)==7,'Wrong inherited external union.')
    require({q['module']:{k:q[k] for k in ['module','object','object_sha256']} for q in tools}==tool_pool and set(tool_pool)=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tool union.')
    require(imports(S)==b['direct_imports'] and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==['LeanProofs.ZFCinPA.'+n for n in PROBES] and len(re.findall(r'^example\b',A.read_text(),re.M))==10,'Wrong audit8/10.')
    for q in [S,A]:require(not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Untrusted proof shortcut/options.')
    selected={q['module']:q for q in reused};external=set(b['direct_external_boundaries']);seen=set();found=set()
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:return
        if m in external:found.add(m);return
        require(m in selected,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for child in imports(selected[m]['source']):visit(child)
    for m in imports(S):visit(m)
    require(seen==set(selected) and found==external and len(external)==6,'Wrong actual import DFS.')
    require(set(external_pool)==external|set(b['inherited_extra_external_modules']) and b['inherited_extra_external_modules']==['Foundation.FirstOrder.Arithmetic.HFS.Seq'],'Wrong retained Seq boundary.')
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
    dep_state=dependency_state();libs=[Path(x) for x in b['libraries']];require(all(x.is_dir() for x in libs),'Missing existing library.')
    overlay=Path(b['namespace_overlay']['source']);require(overlay.is_dir() and b['namespace_overlay']['whole_namespace_independently_attested'] is False,'Wrong overlay boundary.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    (cache/'Foundation').symlink_to(overlay.resolve(),target_is_directory=True)
    for q in reused:
        dst=cache/rel(q['module']);dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(Path(q['object']).resolve())
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss)
    aa=snaps/'Audit.lean';shutil.copyfile(A,aa);pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA)
    search=[cache,*libs,C.parent.parent/'lib/lean']
    def first(m):
        q=next((root/rel(m) for root in search if (root/rel(m)).is_file()),None)
        require(q is not None,'Missing actual provider '+m);return q.resolve()
    def provider_check():
        rows=[]
        for q in reused+providers+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve() and sha(pp)==q['object_sha256'],'Wrong actual first provider '+q['module'])
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=provider_check();env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
    record=dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,
        scope='Native GIC ordered matrix-slot encoding identities for arbitrary internal K, parity vacancy under IΣ2, and the literal padded G instance. No complete native-body encoding equivalence, universal schema closure, proof compiler or consistency endpoint.',
        source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),
        parent_summaries=summaries,parent_snapshots=snapshots,parent_scope=b['scope'],compiler=b['compiler'],compiler_version_query_performed=False,
        reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=31,exact_project_import_closure=sorted(seen),
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
