#!/usr/bin/env python3
"""Unchanged UniformStatement; exact actual providers and explicit historical D1 cached boundary."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-uniform-statement')
MODULE='ZFCinPA.UniformStatement'
PREFIX='LeanProofs.ZFCinPA.'
PROBES=['conZFCBodyF_eq', 'free_fNumF', 'toNat_toSet_congr', 'quote_toSet_congr', 'sealCount_zero', 'sealCount_succ', 'quote_toSet_fAllIter', 'quote_conZFCSet', 'numChainCode_natCast', 'conNumCode_natCast', 'sealCountV_natCast', 'allClosure_natCast', 'conZFCBodyCode_natCast', 'conZFCSetCodeFun.defined', 'eval_conZFCSetCodeGraph_iff', 'conZFCSetCode_total', 'conZFCSetCode_functional', 'conZFCSetCode_existsUnique', 'conZFCSetCodeFun_natCast', 'conZFCSetCode_quote_numeral', 'eval_paUniformZFCProvabilitySentence_iff', 'eval_paUniformZFCProvabilitySentence_iff_fun', 'provable_conZFCSet_standard_point', 'paUniformZFCProvability_standard_instance', 'eval_paUniformZFCProvabilitySentence_iff_selector', 'peano_proves_uniformZFCProvability_of_selectorInAllModels', 'peano_proves_uniformZFCProvability_iff_selectorInAllModels']
SOURCE_SHA='5eb864f392d168148ac7394841cb6de840c473444ec134dbe8f0a3c201c0dcfd'
AUDIT_SHA='0cc6bf218a6866e1eef2aaa81b5800aca7892e2f8199beb84fff3cbbfa712ec2'
BOUNDARY_SHA='dd32e44579a2a6db0a463775035eb9356ff94e89587d70d43dddd68e49c825a7'
PARENT_SHAS=['ed85e9f333195da255e63d598d27d28fe422771b3390643898b79d84eee53279', '6006610b2eeba47ffe9ceaa12740f234b6ec7283f246520f28db5616cf250847', 'd53d5b876a45d9a68d27f7423a8c6cefeaba5b9f48b80538ca256cb0e1b7fc61', 'c6ed6c6bd40da28a3460778686f32cd969fd5695ce89187a72efe19e23c2fadd']
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
    p.add_argument('--source',type=Path,default=HERE/'UniformStatement.lean');p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary.json');p.add_argument('--output',type=Path,required=True)
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
    require([p['record']['sha256']for p in b['parents']]==PARENT_SHAS,'Wrong four-parent identities.')
    parents=[];parent_paths=[]
    for spec in b['parents']:
        E=pin(spec['record']['path'],spec['record']['sha256']);e=json.loads(E.read_text());parents.append(e);parent_paths.append(dict(path=str(E),sha256=spec['record']['sha256']))
        require(e['status']=='PASS'and(e['named_axiom_probes'],e['callers'],e['warnings'])==(spec['probes'],spec['callers'],spec['warnings']),'Wrong actual parent outcome.')
        require(e['before']==e['after']and len(e['before'])==spec['inputs']and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Incomplete parent.')
        require(all(e[k]==v for k,v in spec['policy'].items())and all(k not in e for k in spec['policy_absent']),'Changed or invented parent policy fields.')
        require(all(e[k]==v for k,v in spec['closure'].items())and sorted(q['module']for q in e['reused_modules'])==spec['selected_modules'],'Parent closure metadata changed.')
        require(not e['dependency_build']and not e['downloads'],'Parent execution scope changed.')
        legacy=spec['schema']=='d1_cache_history'
        if legacy:
            require(e['compiler_version_query_performed']is True and(e['per_command_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Historical D1 policy changed.')
            require(e['exact_project_import_closure']is True and e['exact_project_prerequisite_count']==36 and e['warnings']==0,'Historical D1 closure/warnings changed.')
            require(all(k not in e for k in ['source_pass_object','source_object_recorded_before_audit','fresh_first_provider_before_audit','source_pass_artifacts','axiom_reports']),'Invented historical capture.')
        else:
            require(not e['prepare_only']and not e['compiler_version_query_performed']and(e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Modern parent policy changed.')
            if spec['schema']in ['translation','fixedpoint']:
                require(e['source_option_overrides']==({'maxRecDepth':8000}if spec['schema']=='translation'else{})and e['audit_option_overrides']=={}and e['exact_selected_prerequisite_count']==(30 if spec['schema']=='translation'else 0)and e['whole_namespace_cache_attested']is False,'Translation/FixedPoint policy/closure changed.')
                require(all(Path(q['path']).is_symlink()and str(Path(q['path']).resolve())==q['target']for q in e['namespace_mirror_links']),'Parent namespace mirror changed.')
            else:require(spec['schema']=='native_peel'and e['exact_project_prerequisite_count']==13 and 'source_pass_artifacts'not in e,'NativePeel historical schema changed.')
        require(e['source']['sha256']==spec['source_sha256']and e['audit']['sha256']==spec['audit_sha256'],'Parent source/audit identity.')
        if spec['rehash_all_before']:
            for pp,hh in e['before'].items():pin(pp,hh)
        for k in ['source','audit']:pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
        fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']==spec['module'],'Wrong parent fresh module.')
        f=fs[0];pin(f['path'],f['sha256']);require(f['source_sha256']==e['source']['sha256'],'Wrong parent fresh source.')
        if not legacy:
            require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0)and e['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'Parent fresh preaudit capture.')
            if 'source_pass_artifacts'in e:
                require(artifacts(f['path'])==e['source_pass_artifacts']and len(e['source_pass_artifacts'])==(4 if spec['schema']=='fixedpoint'else 1),'Parent companion capture.')
                for x in e['source_pass_artifacts']:pin(x['path'],x['sha256'])
        require([c['label']for c in e['commands']]==['source','audit'],'Parent command order.')
        for c,d in zip(e['commands'],spec['logs'],strict=True):
            log=pin(d['path'],d['sha256'])
            if legacy:require(all(k not in c for k in ['log','log_sha256','interrupted']),'Historical command schema changed.')
            else:require(c['log']==str(log)and c['log_sha256']==d['sha256']and c['interrupted']is None,'Modern raw-log identity changed.')
            expect=[e['compiler']['path']]+([]if legacy else['-j1'])+['-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
            require(c['command']==expect and c['exit_code']==0 and not c['timed_out']and 0<c['seconds']<=120 and log.read_text()==c['output'],'Parent raw command/log mismatch.')
        if not legacy:require(sum(c['seconds']for c in e['commands'])<=120,'Parent shared budget.')
        require([c['output'].count('warning:')for c in e['commands']]==spec['warning_counts']==([13,0]if spec['schema']=='fixedpoint'else[0,0]),'Parent warning history changed.')
        ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(ns==spec['audit_names']and [x['name']for x in rr]==ns and len(rr)==spec['probes']and all(set(x['axioms'])<=STANDARD for x in rr),'Parent raw reports.')
        if not legacy:require(rr==e['axiom_reports'],'Parent recorded reports changed.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==spec['callers'],'Parent typed caller census.')
    require(imports(S)==['ZFCinPA.ZFDelta1', 'ZFCinPA.Translation', 'Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1', 'Foundation.FirstOrder.Bootstrapping.FixedPoint']and imports(A)==[MODULE]and not S.read_text().startswith('module\n'),'Imports/header changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==27,'Audit census/names.')
    for q in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted proof exit.')
    require(re.findall(r'set_option\s+(maxHeartbeats|maxRecDepth)\s+(\S+)',S.read_text())==[('maxRecDepth','8000')]and not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',A.read_text()),'Changed source/audit proof limits.')
    require('set_option maxRecDepth 8000 in\n'in S.read_text()and 'attribute [local irreducible] BoundedZFCConsistency.conZFCForm SetTheory.sealF'in S.read_text(),'Localized source policy changed.')
    reused,external,tools=b['reused_modules'],b['external_project_boundaries'],b['toolchain_providers']
    require([q['module']for q in reused]==['BoundedZFCConsistency.AxiomCode', 'BoundedZFCConsistency.AxiomTruth', 'BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.Choice', 'BoundedZFCConsistency.CodePredicate', 'BoundedZFCConsistency.CodedDerivation', 'BoundedZFCConsistency.CodedRank', 'BoundedZFCConsistency.Coding', 'BoundedZFCConsistency.FormulaClosedSet', 'BoundedZFCConsistency.InternalSat', 'BoundedZFCConsistency.InternalSatTotality', 'BoundedZFCConsistency.InternalSoundness', 'BoundedZFCConsistency.LevelCollapse', 'BoundedZFCConsistency.LevelSoundness', 'BoundedZFCConsistency.LevelSoundnessProof', 'BoundedZFCConsistency.OmegaRecursion', 'BoundedZFCConsistency.UniverseTruthLevel', 'BoundedZFCConsistency.UniverseTruthZero', 'FirstOrder.Calculus', 'FirstOrder.ClassicalCompleteness', 'FirstOrder.Compactness', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'Foundation.FirstOrder.Bootstrapping.FixedPoint', 'Foundation.FirstOrder.SetTheory.Basic', 'Foundation.FirstOrder.SetTheory.Basic.Axioms', 'Foundation.FirstOrder.SetTheory.Basic.Misc', 'Foundation.FirstOrder.SetTheory.Basic.Model', 'Foundation.FirstOrder.SetTheory.Z', 'Foundation.Vorspiel.ExistsUnique', 'ZF.Zf', 'ZFCinPA.Instances', 'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SchemaClosure', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.Translation', 'ZFCinPA.ZFDelta1'],'Wrong selected project subset.')
    require([q['module']for q in external]==['Foundation.FirstOrder.Arithmetic.Basic.Model', 'Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1', 'Foundation.FirstOrder.Bootstrapping.Syntax', 'Foundation.FirstOrder.Completeness.CounterModel', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1', 'Mathlib.Logic.IsEmpty', 'Mathlib.SetTheory.Cardinal.Basic'],'Wrong opaque cached boundary.')
    require([q['module']for q in tools]==['Init'],'Wrong tool boundary.')
    C=pin(b['compiler']['path'],b['compiler']['sha256'])
    require(all(all(e['compiler'][k]==b['compiler'][k]for k in ['path','sha256','version'])for e in parents),'Compiler changed.')
    require(b['provider_owner']=={'BoundedZFCConsistency.AxiomCode': 0, 'BoundedZFCConsistency.AxiomTruth': 0, 'BoundedZFCConsistency.Basic': 0, 'BoundedZFCConsistency.Choice': 0, 'BoundedZFCConsistency.CodePredicate': 0, 'BoundedZFCConsistency.CodedDerivation': 0, 'BoundedZFCConsistency.CodedRank': 0, 'BoundedZFCConsistency.Coding': 0, 'BoundedZFCConsistency.FormulaClosedSet': 0, 'BoundedZFCConsistency.InternalSat': 0, 'BoundedZFCConsistency.InternalSatTotality': 0, 'BoundedZFCConsistency.InternalSoundness': 0, 'BoundedZFCConsistency.LevelCollapse': 0, 'BoundedZFCConsistency.LevelSoundness': 0, 'BoundedZFCConsistency.LevelSoundnessProof': 0, 'BoundedZFCConsistency.OmegaRecursion': 0, 'BoundedZFCConsistency.UniverseTruthLevel': 0, 'BoundedZFCConsistency.UniverseTruthZero': 0, 'FirstOrder.Calculus': 0, 'FirstOrder.ClassicalCompleteness': 0, 'FirstOrder.Compactness': 0, 'FirstOrder.Completeness': 0, 'FirstOrder.Fol': 0, 'Foundation.FirstOrder.Bootstrapping.FixedPoint': 1, 'Foundation.FirstOrder.SetTheory.Basic': 0, 'Foundation.FirstOrder.SetTheory.Basic.Axioms': 0, 'Foundation.FirstOrder.SetTheory.Basic.Misc': 0, 'Foundation.FirstOrder.SetTheory.Basic.Model': 0, 'Foundation.FirstOrder.SetTheory.Z': 0, 'Foundation.Vorspiel.ExistsUnique': 0, 'ZF.Zf': 0, 'ZFCinPA.Instances': 2, 'ZFCinPA.ReplacementDelta1': 2, 'ZFCinPA.SchemaClosure': 2, 'ZFCinPA.SeparationDelta1': 2, 'ZFCinPA.Translation': 0, 'ZFCinPA.ZFDelta1': 2, 'Foundation.FirstOrder.Arithmetic.Basic.Model': 1, 'Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1': 3, 'Foundation.FirstOrder.Bootstrapping.Syntax': 1, 'Foundation.FirstOrder.Completeness.CounterModel': 0, 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1': 2, 'Mathlib.Logic.IsEmpty': 0, 'Mathlib.SetTheory.Cardinal.Basic': 0},'Provider owner selection changed.')
    for q in reused+external:
        e=parents[b['provider_owner'][q['module']]];f=e['fresh_modules'][0]
        if q['module']==f['module']:
            expected=dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
            if 'source_pass_artifacts'in e:expected['artifacts']=e['source_pass_artifacts']
            require(q==expected,'Wrong new fresh pair.')
        else:
            rows=e['reused_modules']+e.get('external_project_boundaries',e.get('providers',[]))
            old=next(x for x in rows if x['module']==q['module']);require(q==old,'Changed inherited pair.')
            for k in ['source','object']:require(e['before'][q[k]]==e['after'][q[k]]==q[k+'_sha256'],'Absent selected parent input.')
            oldfirst=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            op=oldfirst['resolved']if 'resolved'in oldfirst else oldfirst['actual_first']
            require(Path(op).resolve()==Path(q['object']).resolve()and oldfirst['sha256']==q['object_sha256'],'Parent selected first provider.')
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
        if 'artifacts'in q:
            require(artifacts(q['object'])==q['artifacts'],'Changed companions.')
            for x in q['artifacts']:pin(x['path'],x['sha256'])
    require(tools==parents[0]['toolchain_providers'],'Changed inherited tool boundary.')
    for q in tools:
        require(Path(q['object'])==C.parent.parent/'lib/lean'/rel(q['module']),'Tool root mismatch.')
        pin(q['object'],q['object_sha256']);require(artifacts(q['object'])==q['artifacts'],'Tool companion set.')
        for x in q['artifacts']:pin(x['path'],x['sha256'])
    require([q['module']for q in b['current_boundary_companions']]==['Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1', 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1'],'Wrong current-only companion scope.')
    for q in b['current_boundary_companions']:
        old=next(x for x in external if x['module']==q['module'])
        require(artifacts(old['object'])==q['artifacts']and len(q['artifacts'])==4,'Current opaque companions changed.')
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
    targets=[Path(q['module'].replace('.','/')).relative_to('Foundation')for q in reused if q['module'].startswith('Foundation.')]
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
    for q in reused:
        for x in q.get('artifacts',[dict(path=q['object'],sha256=q['object_sha256'])]):
            pp=Path(x['path']);dest=cache/rel(q['module']);dest=dest.parent/pp.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(pp)
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
    pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA);toolroot=C.parent.parent/'lib/lean';search=[cache]+roots+[toolroot]
    def first(m):return next((r/rel(m)).resolve()for r in search if(r/rel(m)).is_file())
    def providers():
        rows=[]
        for q in reused+external+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve()and sha(pp)==q['object_sha256'],'Wrong actual provider.')
            if 'artifacts'in q:require(artifacts(pp)==q['artifacts'],'Selected companion drift.')
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=providers();leanpath=os.pathsep.join(str(x)for x in [cache]+roots);env=dict(os.environ,LEAN_PATH=leanpath,LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=parent_paths,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,external_project_boundaries=external,toolchain_providers=tools,actual_first_providers=actual,exact_selected_import_closure=sorted(seen),exact_selected_prerequisite_count=37,opaque_boundary_modules=sorted(seen_external),whole_namespace_cache_attested=False,source_option_overrides={'maxRecDepth':8000},source_option_scope=b['source_option_scope'],audit_option_overrides={},before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=leanpath,LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['legacy_scope'],selected_provider_owners=b['provider_owner'],current_boundary_companions=b['current_boundary_companions'],all_parent_current_inputs_rehashed=False,namespace_mirrors=[dict(mirror_spec,scratch_tree=str(cache/'Foundation'))],namespace_mirror_links=mirror_links)
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
        post();r.update(status='PASS',named_axiom_probes=27,callers=27,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
