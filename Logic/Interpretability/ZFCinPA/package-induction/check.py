#!/usr/bin/env python3
"""Unchanged PackageInduction; exact actual Uniform parent; default new proof limits and inherited opaque cache scope."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-package-induction')
MODULE='ZFCinPA.PackageInduction'
PREFIX='LeanProofs.ZFCinPA.'
PROBES=['HasZFCConsistencyProofPackage', 'hasZFCConsistencyProofPackage_definable', 'zfcProofSelectorIn_of_package', 'DirectZFCMasterProofPackage', 'directZFCMasterProofPackage_definable', 'zfcProofSelectorIn_of_directMasterProofs']
SOURCE_SHA='c45144c943d1a1c53bd16e8938281fc5fa0e9f59800419a23d636766572f9138'
AUDIT_SHA='0e5a71fccaf0a4fd637ff83024c4d0351fb132565bc1cfcf01e43cc8350f256b'
BOUNDARY_SHA='79d2dc69612c07833a05fa225eec041df671362e9bc9fb0f557a2a3b854bd4f9'
PARENT_SHAS=['1ae70130a1f0898e7a78b4c6f9343c07ac4e4a9ff101655bc5098aa4029ed96f']
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda m,s='.olean':Path(m.replace('.','/')).with_suffix(s)
imports=lambda p:re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def require(x,msg):
    if not x:raise RuntimeError(msg)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def artifacts(p):
    p=Path(p);return [dict(path=str(q.resolve()),sha256=sha(q))for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]if q.is_file()]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'PackageInduction.lean');p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary-v3.json');p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true');a=p.parse_args();require(__debug__,'No optimized Python.')
    S,A,B,W=a.source.resolve(),a.audit.resolve(),a.boundary.resolve(),a.output.resolve()
    require(not W.exists()or(W.is_dir()and not any(W.iterdir())),'Fresh output required.')
    require(not W.is_relative_to(Path('/home/codex/.codex/worktrees/ec20/Proofs'))and not W.is_relative_to(Path('/home/codex/src/Proofs')),'External output only.')
    tracked={}
    def pin(p,h):
        p=Path(p).resolve();require(p.is_file()and sha(p)==h,'Changed input '+str(p))
        require(str(p)not in tracked or tracked[str(p)]==h,'Conflicting identity.');tracked[str(p)]=h;return p
    for p,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(p,h)
    b=json.loads(B.read_text())
    for q in b['static_inputs']+[b['canonical_source']]:pin(q['path'],q['sha256'])
    require(b['source']['sha256']==SOURCE_SHA and b['audit']['sha256']==AUDIT_SHA and b['module']==MODULE,'Boundary identities.')
    require([p['record']['sha256']for p in b['parents']]==PARENT_SHAS,'Wrong sole-parent identity.')
    parents=[];parent_paths=[]
    for spec in b['parents']:
        E=pin(spec['record']['path'],spec['record']['sha256']);e=json.loads(E.read_text());parents.append(e);parent_paths.append(dict(path=str(E),sha256=spec['record']['sha256']))
        require(e['status']=='PASS'and e['before']==e['after']and len(e['before'])==spec['before_count'],'Wrong recorded parent outcome.')
        require(e['compiler']['path']==b['compiler']['path']and e['compiler']['version']==b['compiler']['version']and e['before'][b['compiler']['path']]==b['compiler']['sha256'],'Parent compiler binding.')
        require([{k:v for k,v in c.items()if k!='output'}for c in e['commands']]==spec['commands'],'Historical command metadata drift.')
        for c,d in zip(e['commands'],spec['logs'],strict=True):
            log=pin(d['path'],d['sha256']);require(c['exit_code']==0 and c['seconds']>0 and log.read_text()==c['output'],'Historical raw log drift.')
        require(spec['schema']=='modern_uniform'and(e['named_axiom_probes'],e['callers'],e['warnings'])==(27,27,0)and not e['prepare_only'],'Uniform actual outcome.')
        require(all(e[k]for k in ['only_standard_axioms','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit','source_object_recorded_before_audit']),'Uniform capture flags.')
        require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[])and not e['dependency_build']and not e['downloads']and not e['compiler_version_query_performed'],'Uniform execution policy.')
        require(e['source_option_overrides']==spec['source_option_overrides']=={'maxRecDepth':8000}and e['source_option_scope']==spec['source_option_scope']and e['audit_option_overrides']=={},'Uniform local source-option history.')
        require(e['exact_selected_prerequisite_count']==37 and len(e['reused_modules'])==37 and len(e['external_project_boundaries'])==7 and e['whole_namespace_cache_attested']is False,'Uniform selected scope.')
        require([c['label']for c in e['commands']]==['source','audit']and all(not c['timed_out']and c['interrupted']is None and '-j1'in c['command']and '-M4096'in c['command']for c in e['commands']),'Uniform command states.')
        for pp,hh in e['before'].items():pin(pp,hh)
        for k in ['source','audit']:
            pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
        require(len(e['fresh_modules'])==1,'Uniform fresh count.');f=e['fresh_modules'][0]
        require(f['module']=='ZFCinPA.UniformStatement'and f['source_sha256']==e['source']['sha256']and e['source_pass_object']==dict(f,source_command_index=0),'Uniform source-pass object.')
        require(e['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']}and artifacts(f['path'])==e['source_pass_artifacts'],'Uniform first-provider/companion capture.')
        pin(f['path'],f['sha256'])
        snap=pin(spec['audit_snapshot']['path'],spec['audit_snapshot']['sha256'])
        require(spec['audit_snapshot']['sha256']==e['audit']['sha256']and re.findall(r'^#print axioms (\S+)$',snap.read_text(),re.M)==spec['probe_names'],'Parent audit snapshot.')
        rr=reports(e['commands'][-1]['output']);require(rr==e['axiom_reports']and[q['name']for q in rr]==spec['probe_names']and all(set(q['axioms'])<=STANDARD for q in rr),'Parent exact axiom reports.')
    require(imports(S)==['ZFCinPA.UniformStatement']and imports(A)==[MODULE]and not S.read_text().startswith('module\n'),'Imports/header changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==8,'Audit census/names.')
    for q in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted proof exit.')
    require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',S.read_text()+A.read_text()),'Changed default source/audit proof limits.')
    reused,external,tools=b['reused_modules'],b['external_project_boundaries'],b['toolchain_providers']
    require([q['module']for q in reused]==['BoundedZFCConsistency.AxiomCode', 'BoundedZFCConsistency.AxiomTruth', 'BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.Choice', 'BoundedZFCConsistency.CodePredicate', 'BoundedZFCConsistency.CodedDerivation', 'BoundedZFCConsistency.CodedRank', 'BoundedZFCConsistency.Coding', 'BoundedZFCConsistency.FormulaClosedSet', 'BoundedZFCConsistency.InternalSat', 'BoundedZFCConsistency.InternalSatTotality', 'BoundedZFCConsistency.InternalSoundness', 'BoundedZFCConsistency.LevelCollapse', 'BoundedZFCConsistency.LevelSoundness', 'BoundedZFCConsistency.LevelSoundnessProof', 'BoundedZFCConsistency.OmegaRecursion', 'BoundedZFCConsistency.UniverseTruthLevel', 'BoundedZFCConsistency.UniverseTruthZero', 'FirstOrder.Calculus', 'FirstOrder.ClassicalCompleteness', 'FirstOrder.Compactness', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'Foundation.FirstOrder.Bootstrapping.FixedPoint', 'Foundation.FirstOrder.SetTheory.Basic', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Foundation.FirstOrder.SetTheory.Basic.Misc', 'Foundation.FirstOrder.SetTheory.Basic.Model', 'Foundation.FirstOrder.SetTheory.Z', 'Foundation.Vorspiel.ExistsUnique', 'ZF.Zf', 'ZFCinPA.Instances', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.Translation', 'ZFCinPA.UniformStatement', 'ZFCinPA.ZFDelta1'],'Wrong selected project subset.')
    require([q['module']for q in external]==['Foundation.FirstOrder.Arithmetic.Basic.Model', 'Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Completeness.CounterModel', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Mathlib.Logic.IsEmpty', 'Mathlib.SetTheory.Cardinal.Basic'],'Wrong opaque cached boundary.')
    require([q['module']for q in tools]==['Init'],'Wrong tool boundary.')
    extensions=b['current_only_boundary_artifacts'];current_only={q['module']:q for q in extensions}
    require(list(current_only)==['Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1','Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1']and len(extensions)==2,'Wrong current-only companion extension.')
    require(set(current_only)=={q['module']for q in external if q['module'].startswith('Foundation.')and'artifacts'not in q},'Opaque companion inventory drift.')
    for q in external:
        if q['module']in current_only:
            x=current_only[q['module']]
            require(x['scope']=='Current-only companion observation for this new guard; inherited source/object metadata remains unchanged. No retroactive parent capture or whole-cache attestation.','Companion provenance scope.')
            require(artifacts(q['object'])==x['artifacts']and len(x['artifacts'])==4 and x['artifacts'][0]==dict(path=q['object'],sha256=q['object_sha256']),'Changed current-only artifact family.')
            for item in x['artifacts']:pin(item['path'],item['sha256'])
    def selected_artifacts(q):
        return q['artifacts']if'artifacts'in q else current_only[q['module']]['artifacts']if q['module']in current_only else[dict(path=q['object'],sha256=q['object_sha256'])]
    C=pin(b['compiler']['path'],b['compiler']['sha256'])
    require(b['compiler']['compiler_version_query_performed']is False,'No new compiler query.')
    for q in reused+external:
        owner=b['provider_owner'][q['module']];e=parents[owner]
        fresh=next((x for x in e['fresh_modules']if x['module']==q['module']),None)
        if fresh is not None:
            require(q==dict(module=fresh['module'],source=e['source']['path'],source_sha256=fresh['source_sha256'],object=fresh['path'],object_sha256=fresh['sha256']),'Exact fresh Uniform pair.')
        else:
            candidates=e['reused_modules']+e['external_project_boundaries'];old=next(x for x in candidates if x['module']==q['module'])
            require(q==old,'Changed exact inherited provider metadata.')
            for k in ['source','object']:require(e['before'][q[k]]==e['after'][q[k]]==q[k+'_sha256'],'Absent selected historical input.')
            oldfirst=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(oldfirst['actual_first']).resolve()==Path(q['object']).resolve()and oldfirst['sha256']==q['object_sha256'],'Recorded selected first provider.')
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
        if 'artifacts'in q:
            require(artifacts(q['object'])==q['artifacts']and len(q['artifacts'])==(1 if q['module']=='ZFCinPA.Translation'else 4),'Changed recorded boundary artifact family.')
            for x in q['artifacts']:pin(x['path'],x['sha256'])
    require(tools==parents[0]['toolchain_providers'],'Changed recorded Init pair.')
    for q in tools:
        require(Path(q['object'])==C.parent.parent/'lib/lean'/rel(q['module']),'Tool root mismatch.')
        pin(q['object'],q['object_sha256']);require(artifacts(q['object'])==q['artifacts'],'Tool companion set.')
        for x in q['artifacts']:pin(x['path'],x['sha256'])
    projects={q['module']:q for q in reused};boundaries={q['module']:q for q in external};seen=set();seen_external=set()
    def visit(m):
        if m=='Init':return
        if m in boundaries:seen_external.add(m);return
        require(m in projects,'Unselected source import '+m)
        if m in seen:return
        seen.add(m)
        for n in imports(projects[m]['source']):visit(n)
    for m in imports(S):visit(m)
    require(seen==set(projects)and seen_external==set(boundaries),'Selected import DFS changed.')
    roots=[Path(x).resolve()for x in b['cached_roots']]
    require(b['cached_roots']==parents[0]['LEAN_PATH'].split(os.pathsep)[1:]and all(x.is_dir()for x in roots),'Cached root list changed.')
    require(all(not(x/rel(MODULE)).exists()for x in roots),'Unexpected preexisting target provider.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    # Lean chooses one root per namespace; preserve the opaque cached Foundation
    # branches while reserving exact selected artifacts and the fresh output.
    mirror_spec=b['namespace_mirror'];base=Path(mirror_spec['cached_tree']).resolve()
    require(mirror_spec['namespace']=='Foundation' and base==next(x/'Foundation'for x in roots if(x/'Foundation').is_dir()),'Wrong Foundation mirror root.')
    targets=[Path(q['module'].replace('.','/')).relative_to('Foundation')for q in reused+external if q['module'].startswith('Foundation.')]
    mirror_links=[]
    def mirror(source,dest,relative=Path()):
        dest.mkdir(parents=True,exist_ok=True)
        for item in sorted(source.iterdir()):
            rp=relative/item.name;dd=dest/item.name
            if item.is_dir()and any(t.is_relative_to(rp)for t in targets):mirror(item,dd,rp)
            elif item.is_file()and any(rp.parent==t.parent and item.name.startswith(t.name+'.')for t in targets):continue
            else:
                dd.symlink_to(item.resolve(),target_is_directory=item.is_dir())
                mirror_links.append(dict(path=str(dd),target=str(item.resolve())))
    mirror(base,cache/'Foundation')
    for q in reused+[q for q in external if q['module'].startswith('Foundation.')]:
        for x in selected_artifacts(q):
            pp=Path(x['path']);dest=cache/rel(q['module']);dest=dest.parent/pp.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(pp)
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
    pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA);toolroot=C.parent.parent/'lib/lean';search=[cache]+roots+[toolroot]
    def first(m):return next((r/rel(m)).resolve()for r in search if(r/rel(m)).is_file())
    def providers():
        rows=[]
        for q in reused+external+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve()and sha(pp)==q['object_sha256'],'Wrong actual provider.')
            if 'artifacts'in q:require(artifacts(pp)==q['artifacts'],'Selected companion drift.')
            if q['module']in current_only:
                require(artifacts(pp)==current_only[q['module']]['artifacts'],'Current-only companion drift.')
                for x in current_only[q['module']]['artifacts']:
                    link=(cache/rel(q['module'])).parent/Path(x['path']).name
                    require(link.is_symlink()and link.resolve()==Path(x['path']).resolve()and sha(link)==x['sha256'],'Current-only overlay companion mismatch.')
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=providers();leanpath=os.pathsep.join(str(x)for x in [cache]+roots);env=dict(os.environ,LEAN_PATH=leanpath,LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=parent_paths,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,external_project_boundaries=external,toolchain_providers=tools,actual_first_providers=actual,exact_selected_import_closure=sorted(seen),exact_selected_prerequisite_count=38,opaque_boundary_modules=sorted(seen_external),whole_namespace_cache_attested=False,source_option_overrides={},audit_option_overrides={},before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=leanpath,LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['legacy_scope'],namespace_mirrors=[dict(mirror_spec,scratch_tree=str(cache/'Foundation'))],namespace_mirror_links=mirror_links,current_only_boundary_artifacts=extensions)
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        require(all(Path(q['path']).is_symlink()and str(Path(q['path']).resolve())==q['target']for q in mirror_links),'Namespace mirror changed.')
        r['after']={p:sha(p)for p in tracked};require(r['before']==r['after']and providers()==actual,'Postcheck failed.')
        for q in r['fresh_modules']:require(first(q['module'])==Path(q['path']).resolve()and sha(q['path'])==q['sha256'],'Fresh object changed.')
        if r['fresh_modules']:require(artifacts(r['fresh_modules'][0]['path'])==r['source_pass_artifacts'],'Fresh module companions changed.')
        r['all_input_provider_postchecks']=True
    save()
    try:
        if a.prepare_only:post();save();print(W/'verification.json');return
        deadline=time.monotonic()+120
        def run(label,file,obj=None):
            remaining=deadline-time.monotonic();require(remaining>0,'Shared deadline exhausted.')
            cmd=[str(C),'-j1','-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)]
            start=time.monotonic();proc=subprocess.Popen(cmd,cwd=snaps,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
            timeout=False;interrupted=None
            try:data,_=proc.communicate(timeout=remaining)
            except BaseException as ex:
                timeout=isinstance(ex,subprocess.TimeoutExpired);interrupted=None if timeout else type(ex).__name__
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                data,_=proc.communicate()
            out=data.decode(errors='replace');log=W/(label+'.log');log.write_text(out)
            r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-start,exit_code=proc.returncode,timed_out=timeout,interrupted=interrupted,output=out,log=str(log),log_sha256=sha(log)));save()
            require(not timeout and interrupted is None and proc.returncode==0,'Source/audit failed; output retained.')
            require('sorryAx'not in out and "declaration uses 'sorry'"not in out,'Untrusted output.');return out
        obj=cache/rel(MODULE);require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)
        q=dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=SOURCE_SHA)
        r.update(fresh_modules=[q],source_pass_object=dict(q,source_command_index=0),source_object_recorded_before_audit=True,fresh_first_provider_before_audit=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE))),source_pass_artifacts=artifacts(obj))
        require(first(MODULE)==obj.resolve()and len(r['source_pass_artifacts'])==1,'Fresh first provider/companion capture mismatch.');save()
        out=run('audit',aa);rr=reports(out);require([q['name']for q in rr]==[PREFIX+n for n in PROBES]and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong actual reports.')
        post();r.update(status='PASS',named_axiom_probes=6,callers=8,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
