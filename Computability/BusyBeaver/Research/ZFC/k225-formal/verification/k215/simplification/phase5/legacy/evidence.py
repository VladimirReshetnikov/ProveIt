"""Read-only validation for the phase-five legacy compatibility evidence.
No compiler or archived program is executed. Primary proof provenance remains
in a separately pinned phase-five packet; this packet stores only its ledgers.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, re

PRIMARY, UNION, EXTRA = 184, 199, 15
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
CLIENTS = ('root222', 'root219', 'rootDom', 'rootPerm', 'offset_checker')
CLIENT_PREFIX = 'SetTheory.BusyBeaver.ZFC.LegacyAudit.'
SUPERVISOR_SHA = 'a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
SUFFIXES = {'.olean', '.ilean', '.vo', '.vos', '.vok', '.pyc', '.pyo', '.o', '.so', '.a', '.glob'}

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def save(p, x): Path(p).write_text(json.dumps(x, indent=2) + '\n')
def binary(p): return any(s in SUFFIXES for s in Path(p).suffixes)
def safe(p):
    q=PurePosixPath(p)
    return not q.is_absolute() and '..' not in q.parts and '\\' not in p and not binary(p)

def validate(m):
    J=lambda p:json.loads(m[p])
    result=J('execution/result.json'); inv=J('execution/inventory.json'); done=J('execution/completed.json')
    basis=J('execution/basis-result.json'); old=J('execution/basis-completed.json')
    live=J('execution/basis-review.json'); before=J('execution/before.json'); tool=J('execution/toolchain.json')
    prep=J('preparation/prepared-inventory.json'); pi=prep['primary']; ui=prep['union']
    prepared=J('preparation/prepared.json')
    assert prepared['primary_modules']==PRIMARY and prepared['union_modules']==UNION and prepared['expected_axiom_reports']==5
    for n,h in prepared['files'].items(): assert digest(m['preparation/'+n])==h
    driver_sha=digest(m['preparation/build.py'])
    runner_paths=[p for p,h in before.items()if p.endswith('/build.py')and h==driver_sha]
    assert len(runner_paths)==1
    preparation_dir=Path(runner_paths[0]).parent
    for n in ('build.py','LegacyAudit.lean','prepared-inventory.json'):
        assert before[str(preparation_dir/n)]==digest(m['preparation/'+n])
    assert digest(m['execution/supervisor.py'])==SUPERVISOR_SHA
    assert any(p.endswith('/verification/k215/lean/build.py')and h==SUPERVISOR_SHA for p,h in before.items())
    audit=J('execution/audit/record.json')
    audit_log=Path(audit['log']);assert audit_log.name=='compiler.log'and audit_log.parent.name=='audit'
    run_dir=audit_log.parent.parent
    assert inv==ui and len(pi['modules'])==PRIMARY and len(inv['modules'])==UNION
    assert inv['external_imports']==pi['external_imports']==['Init']
    rows={r['module']:r for r in inv['modules']}; prows={r['module']:r for r in pi['modules']}
    assert len(rows)==UNION and len(prows)==PRIMARY and set(done)==set(rows) and set(old)==set(prows)
    extras=set(rows)-set(prows); assert len(extras)==EXTRA and 'BusyBeaver.ZFC.RMOffsetBisim' in extras
    assert [r for r in inv['modules']if r['module']in prows]==pi['modules']
    seen=set()
    for r in inv['modules']:
        assert set(r['imports'])<=seen|{'Init'};seen.add(r['module'])
    assert result['status']=='PASS' and (result['project_modules'],result['reused_primary_modules'],result['fresh_legacy_modules'])==(UNION,PRIMARY,EXTRA)
    assert result['basis_unchanged'] and result['all_inputs_objects_logs_rechecked_after_audit']
    assert digest(m['execution/inventory.json'])==result['inventory_sha256']
    assert digest(m['execution/completed.json'])==result['completed_sha256']
    assert basis['status']=='PASS' and basis['primary_project_modules']==PRIMARY
    assert basis['basis_unchanged'] and basis['all_private_objects_logs_and_toolchain_rechecked_after_audits']
    assert basis['typed_audits']==2 and basis['axiom_reports']==10
    assert live['status']=='PASS_LIVE_POST_AUDIT_REVIEW' and live['all184_objects_rehashed_after_audits']
    assert live['result_sha256']==digest(m['execution/basis-result.json'])
    assert basis['inventory_sha256']==digest(m['basis/inventory.json']) and J('basis/inventory.json')==pi
    assert basis['completed_sha256']==digest(m['execution/basis-completed.json'])
    assert tool==J('basis/toolchain.json')
    selected={}
    for name in m:
        if name.startswith('execution/attempts/')and name.endswith('/record.json'):
            rec=J(name); selected[rec['module']]=(name,rec)
    assert set(selected)==extras
    fresh_warnings=0; seconds=0
    for mod,r in rows.items():
        rec=done[mod]
        assert rec['status']=='PASS' and rec['source_sha256']==r['source_sha256']
        assert before[r['source']]==r['source_sha256']
        assert rec['dependencies']=={d:done[d]['object_sha256']for d in r['imports']if d in done}
        assert re.fullmatch('[0-9a-f]{64}',rec['object_sha256'])
        if mod in prows:
            assert r==prows[mod] and rec=={**old[mod],'origin':'phase5_primary_hash_bound'}
            continue
        name,record=selected[mod]; assert record==rec and rec['origin']=='legacy_fresh'
        base=name.rsplit('/',1)[0]
        source=m[base+'/'+Path(r['source']).name]; log=m[base+'/compiler.log']
        assert digest(source)==r['source_sha256'] and digest(log)==rec['log_sha256']
        imports=[x for line in source.decode().splitlines()if line.startswith('import ')for x in line[7:].split()]
        assert imports==r['imports']
        source_root=r['source'][:-len(mod.replace('.','/')+'.lean')].rstrip('/')
        cache=run_dir/'objects'
        assert rec['log']==str(run_dir/Path(base).relative_to('execution')/'compiler.log')
        expected=[tool['lean']['path'],'-j1','-M12288','--root='+source_root,'-o',str(cache/(mod.replace('.','/')+'.olean')),r['source']]
        assert rec['command']==expected
        assert rec['compiler_sha256']==tool['lean']['sha256'] and rec['exit_code']==0 and not rec['timed_out']
        assert rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288
        assert rec['source_unchanged'] and rec['dependencies_unchanged']
        text=log.decode(); assert not any(x in text for x in ['sorryAx',"declaration uses 'sorry'",'error:'])
        assert rec['warnings']==text.count('warning:'); fresh_warnings+=rec['warnings'];seconds+=rec['seconds']
    audit=J('execution/audit/record.json'); assert audit==result['audit'] and audit['status']=='PASS'
    src=m['execution/audit/LegacyAudit.lean']; log=m['execution/audit/compiler.log']; text=log.decode()
    assert src==m['preparation/LegacyAudit.lean'] and digest(src)==audit['source_sha256']
    assert digest(log)==audit['log_sha256'] and audit['warnings']==0 and audit['exit_code']==0
    assert not any(x in text for x in ['warning:','error:','sorryAx',"declaration uses 'sorry'"])
    assert audit['dependencies']=={mod:r['object_sha256']for mod,r in done.items()}
    assert audit['compiler_sha256']==tool['lean']['sha256'] and audit['timeout_seconds']==120 and audit['memory_mebibytes']==12288
    directory=str(Path(audit['log']).parent)
    assert audit['command']==[tool['lean']['path'],'-j1','-M12288','--root='+directory,'-o',directory+'/LegacyAudit.olean',directory+'/LegacyAudit.lean']
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)
    assert len(reports)==5 and {n for n,_ in reports}=={CLIENT_PREFIX+c for c in CLIENTS}
    assert audit['expected_axiom_reports']==5 and not audit['timed_out']
    assert all({x.strip()for x in a.split(',')if x.strip()}<=STANDARD for _,a in reports)
    assert audit['reports']==re.findall(r'depends on axioms: \[([^]]*)\]',text)
    return {'status':'PASS_SAVED_LEGACY_RECORDS','primary_modules':PRIMARY,'union_modules':UNION,'fresh_modules':EXTRA,
            'audit_modules':1,'typed_clients':5,'axiom_reports':5,'fresh_project_warnings':fresh_warnings,'fresh_module_seconds':seconds,
            'scope':'Archived record consistency and15 fresh source/log bindings; primary proof evidence is separately hash-linked. No live compiled-object claim.'}

def collect(run, basis, preparation):
    m={}
    def add(name,p):
        assert safe(name) and name not in m and not p.is_symlink();m[name]=p.read_bytes()
    for p in sorted(run.rglob('*')):
        if p.is_file() and 'objects'not in p.relative_to(run).parts and not binary(p.name):add('execution/'+p.relative_to(run).as_posix(),p)
    for n in ('inventory.json','toolchain.json'):add('basis/'+n,basis/n)
    for n in ('build.py','LegacyAudit.lean','prepared-inventory.json','prepared.json','driver-from-phase4.diff','README.md','evidence.py','review.py','review_saved.py','publish.py'):
        add('preparation/'+n,preparation/n)
    for p in sorted((preparation/'history/publication-v1').rglob('*')):
        if p.is_file(): add('preparation/history/publication-v1/'+p.relative_to(preparation/'history/publication-v1').as_posix(),p)
    if (preparation/'controls.json').exists():add('preparation/controls.json',preparation/'controls.json')
    return m

def live_check(run,basis,preparation):
    m=collect(run,basis,preparation); result=validate(m)
    assert Path(read(run/'audit/record.json')['log']).parent.parent==run
    assert not any(p.is_symlink()and p.is_dir()for p in (run/'objects').rglob('*'))
    for p,h in read(run/'before.json').items():assert sha(p)==h,p
    done=read(run/'completed.json'); old=read(run/'basis-completed.json')
    inv=read(run/'inventory.json')
    for r in inv['modules']:
        rec=done[r['module']];assert sha(r['source'])==r['source_sha256']
        obj=run/'objects'/(r['module'].replace('.','/')+'.olean')
        assert sha(obj)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
        if r['module']in old:
            provider=basis/'objects'/(r['module'].replace('.','/')+'.olean')
            assert obj.is_symlink() and obj.resolve(strict=True)==provider.resolve(strict=True)
            assert sha(provider)==old[r['module']]['object_sha256']
        else: assert not obj.is_symlink()
    expected={mod.replace('.','/')+'.olean'for mod in done}
    assert {p.relative_to(run/'objects').as_posix()for p in (run/'objects').rglob('*')if p.is_file()}==expected
    a=read(run/'audit/record.json');assert sha(run/'audit/LegacyAudit.olean')==a['object_sha256']
    assert collect(run,basis,preparation)==m
    return m,{**result,'status':'PASS_LIVE_LEGACY_POST_AUDIT_REVIEW','all199_objects_rehashed_after_audit':True,
              'basis184_unchanged':True,'result_sha256':sha(run/'result.json'),
              'evidence_manifest':{n:{'sha256':digest(b),'bytes':len(b)}for n,b in sorted(m.items())}}
