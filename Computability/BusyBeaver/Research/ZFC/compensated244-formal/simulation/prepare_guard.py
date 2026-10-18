from pathlib import Path
import hashlib,json,re,ast,difflib
H=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();parents={};pool={};tools={}
for key,p,prefix in [('positive',Path('/tmp/zfc244-positive-blocks/run2/verification.json'),''),('invariant',Path('/tmp/zfc244-routing245-invariant/run1/verification.json'),'SetTheory.BusyBeaver.ZFC.Routing245Invariant.'),('blocks',H.parent/'blocks/run1/verification.json','')]:
 e=json.loads(p.read_text());auditnames=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
 parents[key]=dict(path=str(p),sha256=sha(p),probes=e['named_axiom_probes'],callers=e['callers'],audit_names=auditnames,report_names=[prefix+n for n in auditnames],tools=sorted(q['module']for q in e['toolchain_providers']))
 for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])for f in e['fresh_modules']]:
  row={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']}
  if q['module']in pool:assert pool[q['module']]==row
  pool[q['module']]=row
 for q in e['toolchain_providers']:
  row={k:q[k]for k in ['module','object','object_sha256']}
  if q['module']in tools:assert tools[q['module']]==row
  tools[q['module']]=row
assert len(pool)==7 and len(tools)==2
b=dict(parents=parents,compiler=e['compiler'],reused_modules=list(pool.values()),toolchain_providers=list(tools.values()),scope='Exact three fresh prerequisite records and their seven-project union; all small parent input snapshots rehashed, no broad851-project replay.',static_inputs=[dict(path=str(H/'prepare_source.py'),sha256=sha(H/'prepare_source.py'))])
(H/'boundary.json').write_text(json.dumps(b,indent=2)+'\n')
s=Path('/tmp/zfc244-positive-blocks/check.py').read_text().replace('Positive-block halting equivalence; exactly Core+RuntimePerm252, no builds.','Concrete compensated244 whole-run simulation; exact three parents/seven projects.')
s=s.replace('/tmp/zfc244-positive-blocks','/tmp/zfc244-compensated-lean/simulation').replace('BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.Compensated244Simulation').replace("HERE/'PositiveBlockBisimulation.lean'","HERE/'Compensated244Simulation.lean'")
s=re.sub(r'^PROBES=.*$',"PROBES=['simulation','start_halts_iff','blank_halts_iff','blank_nonhalts_iff']",s,flags=re.M)
for key,p in [('SOURCE_SHA',H/'Compensated244Simulation.lean'),('AUDIT_SHA',H/'Audit.lean'),('BOUNDARY_SHA',H/'boundary.json')]:s=re.sub(r'^'+key+r'=.*$',key+'='+repr(sha(p)),s,flags=re.M)
s=re.sub(r'^PARENT_SHA=.*$', 'PARENT_SHAS='+repr({k:d['sha256']for k,d in parents.items()}),s,flags=re.M)
s=s.replace("    p.add_argument('--parent-evidence',type=Path)\n",'')
a=s.index('    b=json.loads(B.read_text());E=pin');z=s.index('    seen=set();toolnames=',a)
s=s[:a]+'''    b=json.loads(B.read_text())
    for q in b['static_inputs']:pin(q['path'],q['sha256'])
    C=pin(b['compiler']['path'],b['compiler']['sha256']);pool={};alltools={};parent_records=[]
    for key,desc in b['parents'].items():
        E=pin(desc['path'],PARENT_SHAS[key]);require(desc['sha256']==PARENT_SHAS[key],'Parent boundary mismatch.');e=json.loads(E.read_text())
        require(e['status']=='PASS'and(e['named_axiom_probes'],e['callers'])==(desc['probes'],desc['callers']),'Wrong parent outcome.')
        require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete parent.')
        require([q['label']for q in e['commands']]==['source','audit']and all(q['exit_code']==0 and not q.get('timed_out',False)for q in e['commands']),'Failed parent commands.')
        require(all(e['compiler'][k]==b['compiler'][k]for k in ['path','version','sha256']),'Compiler identity differs.')
        for pp,h in e['before'].items():pin(pp,h)
        for k in ['source','audit']:pin(e[k]['snapshot'],e[k]['sha256'])
        ns=re.findall(r'^#print axioms (\\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(ns==desc['audit_names']and len(ns)==desc['probes']and [q['name']for q in rr]==desc['report_names']and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong raw parent audit names/axioms.')
        require(len(re.findall(r'^example\\b',Path(e['audit']['snapshot']).read_text(),re.M))==desc['callers'],'Wrong parent callers.')
        if key=='invariant':
            require(desc['report_names']==['SetTheory.BusyBeaver.ZFC.Routing245Invariant.'+n for n in ns]and 'open SetTheory.BusyBeaver.ZFC.Routing245Invariant' in Path(e['audit']['snapshot']).read_text(),'Unexpected invariant namespace.')
        else:require(desc['report_names']==ns,'Unexpected parent namespace.')
        fs=e['fresh_modules'];require(len(fs)==1,'Wrong parent fresh count.');f=fs[0]
        require(e['source_object_recorded_before_audit']and all(e['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256']),'Missing parent fresh capture.')
        require(e['source_pass_object']['source_command_index']==0 and f['source_sha256']==e['source']['sha256'],'Wrong source capture binding.')
        cap=e['fresh_first_provider_before_audit'];require(cap['module']==f['module']and Path(cap['path']).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'],'Fresh parent first mismatch.');pin(f['path'],f['sha256'])
        for q in e['reused_modules']:
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent parent import input.')
            actual=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(actual['actual_first']).resolve()==Path(q['object']).resolve()and actual['sha256']==q['object_sha256'],'Wrong historical first import.')
        for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
            row={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']}
            require(q['module']not in pool or pool[q['module']]==row,'Conflicting shared project pair.');pool[q['module']]=row
        require(sorted(q['module']for q in e['toolchain_providers'])==desc['tools'],'Wrong parent tool selection.')
        for q in e['toolchain_providers']:
            row={k:q[k]for k in ['module','object','object_sha256']};pp=pin(q['object'],q['object_sha256'])
            require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')
            require(q['module']not in alltools or alltools[q['module']]==row,'Conflicting tool identity.');alltools[q['module']]=row
        parent_records.append(dict(path=str(E),sha256=PARENT_SHAS[key],module=f['module']))
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(projects==pool and len(pool)==7 and {q['module']:q for q in tools}==alltools and set(alltools)=={'Init','Lean.Elab.Tactic.Omega'},'Wrong seven-project/two-tool union.')
    require(imports(S)==['BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.Routing245Invariant','BusyBeaver.ZFC.Compensated244Blocks']and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\\b',A.read_text(),re.M))==4,'Wrong audit4/4.')
    for pp in [S,A]:
        require(not re.search(r'\\b(sorry|admit|native_decide)\\b',pp.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\\s+(maxHeartbeats|maxRecDepth)',pp.read_text()),'Raised proof limits.')
''' +s[z:]
s=s.replace("scope='Generic positive-block halting equivalence for Core finite-support tapes. No concrete244 simulation claimed.'","scope='Concrete244 versus checked245 positive-block simulation, arbitrary finite-support start tapes and exact blank halting/nonhalting iff. No PA internalization or infinite-support tape claim.'")
s=s.replace("provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)]","provider_evidence=parent_records").replace('exact_project_prerequisite_count=2','exact_project_prerequisite_count=7')
ast.parse(s);(H/'check.py').write_text(s)
(H/'guard-from-positive.diff').write_text(''.join(difflib.unified_diff(Path('/tmp/zfc244-positive-blocks/check.py').read_text().splitlines(True),s.splitlines(True),fromfile='Positive/check.py',tofile='Simulation/check.py')))
print(json.dumps({p.name:sha(p)for p in [H/'check.py',H/'boundary.json',H/'Compensated244Simulation.lean',H/'Audit.lean']}))
