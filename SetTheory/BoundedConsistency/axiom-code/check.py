#!/usr/bin/env python3
"""Unchanged internal ZFC-axiom codes and bounded axiom-context sentence; seventeen actual Core providers and Init."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-bounded-axiom-code')
MODULE='BoundedZFCConsistency.AxiomCode'
PREFIX='LeanProofs.BoundedZFCConsistency.'
PROBES=['isTwoMap_iff', 'fTwoMapF_spec', 'tmplCode_eq_formCode', 'fTmplCodeF_spec', 'sepCodeV_formCode', 'replCodeV_formCode', 'sepCodeV_isFormCodeSem', 'replCodeV_isFormCodeSem', 'fSepCodeF_spec', 'fReplCodeF_spec', 'fZFCAxiomCodeF_spec', 'isZFCAxiomCode_of_ZFCax', 'fCtxZFCAxiomsF_spec', 'ctxZFCAxioms_ctxCode', 'conZFCBodyF_spec', 'sentence_conZFCForm', 'sat_conZFCForm_iff', 'no_bounded_refutation_nil_of_conZFC', 'zfcprov_conZFCForm_of_valid', 'zfcprov_conZFCForm_of_no_bounded_refutation']
SOURCE_SHA='43fc00e6be27a16f7ae7cd1af7f5ac56fa8f750991b0f9383208d7e66962f0bd'
AUDIT_SHA='16b71fd7f8996b3b7aae23d4ec79a7d0ba2e9e003f2fae88fb165991488e44f2'
BOUNDARY_SHA='89d9bacd19fd6e09dda3a84685bb2d03e9a85eb434081c86dc0653e9ea85bbe8'
PARENT_SHA='2b5e52990c4e3f3c9f8d3056a2ab624ecb4cbee8eec9df3dc37f5f1baa683c1b'
PARENT_SOURCE_SHA='61b6ddd3ecfab0ef267b93d6bed3ed8074041d2580be3efd130d9e1d2d7f48a6'
PARENT_AUDIT_SHA='57f78eb5f3eaffd59196177049a9de8032e85123065d4d6bb9d6e52a81dc4e63'
PARENT_AUDIT_NAMES=['LeanProofs.BoundedZFCConsistency.fRanksF_spec', 'LeanProofs.BoundedZFCConsistency.rankTotal_of_isFormCodeSem', 'LeanProofs.BoundedZFCConsistency.rankUnique_of_isFormCodeSem', 'LeanProofs.BoundedZFCConsistency.ranks_formCode_iff', 'LeanProofs.BoundedZFCConsistency.quantBounded_formCode_iff', 'LeanProofs.BoundedZFCConsistency.quantBounded_imp', 'LeanProofs.BoundedZFCConsistency.quantBounded_all', 'LeanProofs.BoundedZFCConsistency.rankRen_of_isFormCodeSem', 'LeanProofs.BoundedZFCConsistency.quantBounded_of_renames', 'LeanProofs.BoundedZFCConsistency.derStep_of_derStepBounded', 'LeanProofs.BoundedZFCConsistency.derStepBounded_of_derAllBounded', 'LeanProofs.BoundedZFCConsistency.conBodyF_spec', 'LeanProofs.BoundedZFCConsistency.sentence_conForm', 'LeanProofs.BoundedZFCConsistency.sat_logicConForm_iff', 'LeanProofs.BoundedZFCConsistency.zfcprov_logicConForm_of_valid', 'LeanProofs.BoundedZFCConsistency.zfcprov_logicConForm_of_no_bounded_refutation']
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda m,s='.olean':Path(m.replace('.','/')).with_suffix(s)
imports=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def require(x,msg):
    if not x:raise RuntimeError(msg)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'AxiomCode.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary.json')
    p.add_argument('--parent-evidence',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true')
    a=p.parse_args();require(__debug__,'No optimized Python.')
    require(isinstance(SOURCE_SHA,str) and isinstance(BOUNDARY_SHA,str),'Pending generated source/boundary pins: root emission required.')
    S,A,B,W=a.source.resolve(),a.audit.resolve(),a.boundary.resolve(),a.output.resolve()
    require(not W.exists()or(W.is_dir()and not any(W.iterdir())),'Fresh output required.')
    require(not W.is_relative_to(Path('/home/codex/.codex/worktrees/ec20/Proofs')) and not W.is_relative_to(Path('/home/codex/src/Proofs')),'External output only.')
    tracked={}
    def pin(p,h):
        p=Path(p).resolve();require(p.is_file()and sha(p)==h,'Changed input '+str(p))
        require(str(p)not in tracked or tracked[str(p)]==h,'Conflicting identity.')
        tracked[str(p)]=h;return p
    for p,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(p,h)
    b=json.loads(B.read_text())
    for q in b['static_inputs']:pin(q['path'],q['sha256'])
    E=pin(a.parent_evidence or b['parent']['path'],PARENT_SHA);e=json.loads(E.read_text())
    require(b['parent']['sha256']==PARENT_SHA and e['status']=='PASS' and not e['prepare_only'] and (e['named_axiom_probes'],e['callers'])==(16,16),'Wrong parent.')
    require(e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
    require(e['exact_project_import_closure']==sorted(q['module']for q in e['reused_modules']) and e['exact_project_prerequisite_count']==len(e['reused_modules'])==16 and e['external_project_boundaries']==[],'Wrong parent modern Core closure schema.')
    require((e['warnings'],e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(0,120,4096,'1',[]) and e['source_option_overrides']=={'maxRecDepth':8000} and e['audit_option_overrides']=={},'Parent policy changed.')
    require(not any(e[k]for k in ['compiler_version_query_performed','dependency_build','downloads']) and e['compiler']['compiler_version_query_performed'] is False and len(e['LEAN_PATH'].split(os.pathsep))==1,'Parent execution scope changed.')
    require(e['source']['sha256']==PARENT_SOURCE_SHA and e['audit']['sha256']==PARENT_AUDIT_SHA,'Parent source/audit identity mismatch.')
    require(len(e['before'])==90,'Parent recorded input census changed.')
    for pp,hh in e['before'].items():pin(pp,hh)
    for k in ['source','audit']:
        pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
    fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']=='BoundedZFCConsistency.CodedRank','Wrong parent fresh module.')
    f=fs[0];pin(f['path'],f['sha256'])
    require(f['source_sha256']==PARENT_SOURCE_SHA and e['source_object_recorded_before_audit'] and e['source_pass_object']==dict(f,source_command_index=0),'Wrong parent source capture.')
    require(e['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'Wrong parent preaudit capture.')
    require(Path(e['LEAN_PATH'])/rel(f['module'])==Path(f['path']),'Wrong fresh provider cache path.')
    require([q['label']for q in e['commands']]==['source','audit'],'Wrong parent command order.')
    for c in e['commands']:
        log=pin(c['log'],c['log_sha256'])
        expect=[e['compiler']['path'],'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']] if c['label']=='source' else [])+[e[c['label']]['snapshot']]
        require(c['command']==expect and c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None and c['seconds']>0,'Parent command failure/scope.')
        require(log.read_text()==c['output'] and c['output'].count('warning:')==0,'Parent raw log mismatch.')
    require(sum(c['seconds']for c in e['commands'])<=120,'Parent shared budget.')
    ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
    require(ns==PARENT_AUDIT_NAMES and [q['name']for q in rr]==ns and rr==e['axiom_reports'] and all(set(q['axioms'])<=STANDARD for q in rr),'Parent raw reports.')
    require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==16,'Parent caller census.')
    require(imports(S)==['BoundedZFCConsistency.CodedRank']and imports(A)==[MODULE],'Imports changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES],'Audit qualified names changed.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M))==20,'Typed callers changed.')
    for p in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text()),'Untrusted proof exit.')
    require(re.findall(r'set_option\s+(maxHeartbeats|maxRecDepth)\s+(\S+)',S.read_text())==[('maxRecDepth','8000')] and not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',A.read_text()),'Changed existing source/audit limits.')
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(len(reused)==17 and set(projects)==set(['BoundedZFCConsistency.Basic', 'BoundedZFCConsistency.Choice', 'BoundedZFCConsistency.CodePredicate', 'BoundedZFCConsistency.CodedDerivation', 'BoundedZFCConsistency.CodedRank', 'BoundedZFCConsistency.Coding', 'BoundedZFCConsistency.FormulaClosedSet', 'BoundedZFCConsistency.InternalSat', 'BoundedZFCConsistency.InternalSatTotality', 'BoundedZFCConsistency.InternalSoundness', 'BoundedZFCConsistency.OmegaRecursion', 'FirstOrder.Calculus', 'FirstOrder.ClassicalCompleteness', 'FirstOrder.Compactness', 'FirstOrder.Completeness', 'FirstOrder.Fol', 'ZF.Zf']) and b['external_project_boundaries']==[],'Wrong selected projects.')
    C=pin(b['compiler']['path'],b['compiler']['sha256']);require(b['compiler']==e['compiler'],'Different compiler.')
    for q in reused:
        if q['module']==f['module']:
            require(q==dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256']),'Changed fresh pair.')
            for k in ['source','object']:pin(q[k],q[k+'_sha256'])
        else:
            old=next(x for x in e['reused_modules']if x['module']==q['module']);require(q==old,'Changed inherited pair.')
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent inherited input.')
            old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(old['actual_first']).resolve()==Path(q['object']).resolve() and old['sha256']==q['object_sha256'],'Wrong historical first provider.')
    require(tools==e['toolchain_providers'] and len(tools)==1 and tools[0]['module']=='Init','Wrong tool boundary.')
    for q in tools:
        pp=pin(q['object'],q['object_sha256']);require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')
        require(e['before'].get(str(pp))==e['after'].get(str(pp))==q['object_sha256'],'Absent parent tool input.')
        old=next(x for x in e['actual_first_providers']if x['module']==q['module']);require(Path(old['actual_first']).resolve()==pp and old['sha256']==q['object_sha256'],'Parent tool first provider.')
    seen=set();toolnames={'Init'}
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:toolnames.add(m);return
        require(m in projects,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for n in imports(projects[m]['source']):visit(n)
    for m in imports(S):visit(m)
    require(seen==set(projects)and toolnames=={q['module']for q in tools},'Wrong DFS.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    for q in reused:
        dest=cache/rel(q['module']);dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
    pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA);toolroot=C.parent.parent/'lib/lean'
    def first(m):return next((r/rel(m)).resolve()for r in [cache,toolroot]if(r/rel(m)).is_file())
    def providers():
        rows=[]
        for q in reused+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve()and sha(pp)==q['object_sha256'],'Wrong actual provider.')
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=providers();env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope='Internal ZFC-axiom code predicate with seven fixed quotations and two arbitrary-internal-code schemas; exact axiom-context bounded-consistency sentence and a conditional all-model/completeness bridge. No proof of the semantic no-refutation premise, axiom truth in a structure, reflection, or final PA/binary endpoint.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=17,external_project_boundaries=[],source_option_overrides={'maxRecDepth':8000},audit_option_overrides={},before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['scope'])
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        r['after']={p:sha(p)for p in tracked};require(r['before']==r['after']and providers()==actual,'Postcheck failed.')
        for q in r['fresh_modules']:require(first(q['module'])==Path(q['path']).resolve()and sha(q['path'])==q['sha256'],'Fresh object changed.')
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
        r.update(fresh_modules=[q],source_pass_object=dict(q,source_command_index=0),source_object_recorded_before_audit=True,fresh_first_provider_before_audit=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE))))
        require(first(MODULE)==obj.resolve(),'Fresh first provider mismatch.');save()
        out=run('audit',aa);rr=reports(out);require([q['name']for q in rr]==[PREFIX+n for n in PROBES]and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong actual reports.')
        post();r.update(status='PASS',named_axiom_probes=20,callers=20,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
