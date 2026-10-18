from pathlib import Path
import hashlib,json,re,ast,difflib
H=Path(__file__).parent;sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();E=H.parent/'table/run1/verification.json';e=json.loads(E.read_text());assert sha(E)=='53745001227efd76940fa164e66dd78c34a0c276eca1deca83c56947d613f22e'
f=e['fresh_modules'][0];rows=e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]
b=dict(parent=dict(path=str(E),sha256=sha(E)),compiler=e['compiler'],reused_modules=rows,toolchain_providers=e['toolchain_providers'],scope='Exact actual Table244 with fresh pre-audit capture; Core/Table245 reuse from its checked parent. No broad endpoint closure.',static_inputs=[dict(path=str(p),sha256=sha(p))for p in [H/'source-inventory.json',H/'prepare_source.py',H/'prepare_endpoint_successor.py',H/'history/unexecuted-seven-pair-draft/source-inventory.json']])
(H/'boundary.json').write_text(json.dumps(b,indent=2)+'\n')
s=Path('/tmp/zfc244-positive-blocks/check.py').read_text();s=s.replace('Positive-block halting equivalence; exactly Core+RuntimePerm252, no builds.','Seven exact compensated244 blocks and their endpoints; three project providers.')
s=s.replace('/tmp/zfc244-positive-blocks','/tmp/zfc244-compensated-lean/blocks').replace('BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.Compensated244Blocks').replace("HERE/'PositiveBlockBisimulation.lean'","HERE/'Compensated244Blocks.lean'")
probes=[n.removeprefix('SetTheory.BusyBeaver.ZFC.Compensated244Blocks.')for n in re.findall(r'^#print axioms (\S+)$',(H/'Audit.lean').read_text(),re.M)];assert len(probes)==14
s=re.sub(r'^PROBES=.*$','PROBES='+repr(probes),s,flags=re.M)
for key,p in [('SOURCE_SHA',H/'Compensated244Blocks.lean'),('AUDIT_SHA',H/'Audit.lean'),('BOUNDARY_SHA',H/'boundary.json'),('PARENT_SHA',E)]:s=re.sub(r'^'+key+r'=.*$',key+'='+repr(sha(p)),s,flags=re.M)
s=s.replace("b=json.loads(B.read_text());E=pin", "b=json.loads(B.read_text())\n    for q in b['static_inputs']:pin(q['path'],q['sha256'])\n    E=pin")
s=s.replace("==(11,11),'Wrong parent.'","==(53,6),'Wrong parent.'").replace('len(ns)==11','len(ns)==53')
s=s.replace("imports(S)==['BusyBeaver.ZFC.RuntimePerm252']","imports(S)==['BusyBeaver.ZFC.TableCompensated244']")
s=s.replace("==PROBES,'Audit short names changed.'","==[PREFIX+n for n in PROBES],'Audit names changed.'")
s=s.replace("==4,'Typed callers changed.'","==14,'Typed callers changed.'")
s=s.replace("len(reused)==2 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.RuntimePerm252'}","len(reused)==3 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRouting245','BusyBeaver.ZFC.TableCompensated244'}")
a=s.index('    for q in reused:\n        old=next(');z=s.index('    require(tools==',a)
s=s[:a]+'''    for q in reused:
        if q['module'] == 'BusyBeaver.ZFC.TableCompensated244':
            fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']==q['module'],'Wrong fresh parent module.')
            f=fs[0];require(q['source']==e['source']['path']and q['source_sha256']==e['source']['sha256']==f['source_sha256']and q['object']==f['path']and q['object_sha256']==f['sha256'],'Fresh parent identity mismatch.')
            for k in ['source','object']:pin(q[k],q[k+'_sha256'])
            require(e['source_object_recorded_before_audit']and all(e['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256']),'Missing fresh pre-audit capture.')
            cap=e['fresh_first_provider_before_audit'];require(cap['module']==q['module']and Path(cap['path']).resolve()==Path(q['object']).resolve()and cap['sha256']==q['object_sha256'],'Wrong fresh first provider.')
        else:
            old=next(x for x in e['reused_modules']if x['module']==q['module']);require(q==old,'Changed selected parent pair.')
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent parent pair input.')
            old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(old['actual_first']).resolve()==Path(q['object']).resolve()and old['sha256']==q['object_sha256'],'Wrong historical first provider.')
''' +s[z:]
s=s.replace("scope='Generic positive-block halting equivalence for Core finite-support tapes. No concrete244 simulation claimed.'","scope='Seven paired positive blocks and seven new endpoint identities on arbitrary Core finite-support tapes; explicit finite read premises; no whole-run theorem.'")
s=s.replace('exact_project_prerequisite_count=2','exact_project_prerequisite_count=3').replace('named_axiom_probes=4,callers=4','named_axiom_probes=14,callers=14')
ast.parse(s);(H/'check.py').write_text(s)
(H/'guard-from-positive.diff').write_text(''.join(difflib.unified_diff(Path('/tmp/zfc244-positive-blocks/check.py').read_text().splitlines(True),s.splitlines(True),fromfile='Positive/check.py',tofile='Blocks/check.py')))
print(json.dumps({p.name:sha(p)for p in [H/'check.py',H/'boundary.json',H/'Compensated244Blocks.lean',H/'Audit.lean']}))
