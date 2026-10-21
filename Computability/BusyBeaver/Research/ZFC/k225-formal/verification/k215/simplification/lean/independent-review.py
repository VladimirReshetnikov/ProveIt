from pathlib import Path, PurePosixPath
import hashlib,json,re,tarfile

REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PUB=REPO/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/lean'
WORK=Path('/tmp/k215-proof-simplification/root')
BASE=Path('/tmp/k215-lean-complete')
OUT=Path('/tmp/k215-simplification-lean-peer')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
hb=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
result=read(PUB/'result.json');done=read(WORK/'completed.json');baseline=read(BASE/'completed.json')
assert result['status']=='PASS_INCREMENTAL_KERNEL' and not result['new_full_replay']
rows={r['module']:r for r in result['module_evidence']}
assert len(rows)==len(result['module_evidence'])==215
assert len(baseline)==204
archive=PUB/'execution.tar.gz'
assert sha(archive)==result['execution_archive_sha256']
index=read(PUB/'execution-index.json')
with tarfile.open(archive) as t:
    members=t.getmembers();assert len({m.name for m in members})==len(members)==len(index)
    data={}
    for m in members:
        p=PurePosixPath(m.name)
        assert m.isfile() and not p.is_absolute() and '..' not in p.parts
        assert not any(p.name.endswith(x) for x in ('.olean','.olean.server','.olean.private','.ilean','.ir','.o','.so','.vo','.vos','.vok'))
        b=t.extractfile(m).read();assert hb(b)==index[m.name];data[m.name]=b
assert set(data)==set(index)

def clean(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        elif text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
        else:out.append(text[i]);i+=1
    assert depth==0
    return ''.join(out)

imports={};current_objects={};sources={};logs={};origins={};warning_sum=0
for module,row in rows.items():
    source=REPO/row['source'];sources[module]=sha(source)
    assert sources[module]==row['source_sha256']
    text=clean(source.read_text())
    actual=[x for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',text,re.M) for x in line.split()]
    assert actual==row['imports'],module
    imports[module]=actual
    deps={d:rows[d]['object_sha256'] for d in actual if d in rows}
    assert row['dependencies']==deps==done[module]['dependencies'],module
    obj=WORK/'objects'/(module.replace('.','/')+'.olean')
    current_objects[module]=sha(obj)
    assert current_objects[module]==row['object_sha256']==done[module]['object_sha256']
    assert done[module]['status']=='PASS' and done[module]['exit_code']==0 and not done[module]['timed_out']
    assert done[module]['source_sha256']==row['source_sha256']
    for path,digest in done[module]['companions'].items():assert sha(path)==digest
    if row['compilation_origin'].startswith('fresh baseline'):
        prior=baseline[module];assert prior==done[module]
        log=Path(prior['log']).read_bytes();origins[module]='baseline'
    else:
        prefix=row['compilation_origin'].split('execution.tar.gz/')[1]
        rec=json.loads(data[prefix+'/record.json'])
        for k in ('source_sha256','dependencies','module','log_sha256'):assert rec[k]==done[module][k]
        assert rec['status']=='PASS' and rec['exit_code']==0 and not rec['timed_out']
        assert hb(data[prefix+'/'+source.name])==row['source_sha256']
        root=str(source)[:-len(module.replace('.','/')+'.lean')].rstrip('/')
        assert rec['command']==['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M12288','--root='+root,'-o',str(obj),str(source)]
        log=data[prefix+'/compiler.log'];origins[module]=prefix
    assert hb(log)==row['log_sha256'];assert log.decode().count('warning:')==row['warnings']
    logs[module]=hb(log)
    if row['primary_endpoint']:warning_sum+=row['warnings']

def closure(start):
    seen=set();active=set();external={'Init'}
    def go(m):
        if m not in rows:
            assert m=='Init' or m.startswith('Init.'),m
            external.add(m);return
        if m in seen:return
        assert m not in active
        active.add(m)
        for d in imports[m]:go(d)
        active.remove(m);seen.add(m)
    go(start);return seen,external
primary,external=closure('BusyBeaver.ZFC.KEndpoint215')
assert len(primary)==201 and primary=={m for m,r in rows.items() if r['primary_endpoint']}
assert len(set(rows)-primary)==14 and external=={'Init'}
assert warning_sum==result['primary_project_warnings']==31
for m in rows:closure(m)
# Independently verify all original baseline objects and recorded companions remain unchanged.
for m,r in baseline.items():
    assert sha(BASE/'workspace/.lake/build/lib/lean'/(m.replace('.','/')+'.olean'))==r['object_sha256']
    for p,digest in r['companions'].items():assert sha(p)==digest
bfinal=read(BASE/'final-review.json')
assert sha(BASE/'completed.json')==bfinal['completed_sha256']
boundary=read(BASE/'toolchain-boundary-v5.json')
for key in ('lean','lake','Init.olean'):
    row=boundary[key];assert sha(row['path'])==row['sha256']
assert boundary['lean']['sha256']==result['compiler_sha256']
# Check the two raw typed clients and all ten reports, not only their summaries.
audits={}
for name,expected in [('EndpointAudit215',2),('K215Audit',8)]:
    rec=read(PUB/(name+'.json'));src=PUB/(name+'.lean');log=PUB/(name+'.log')
    assert rec['status']=='PASS' and rec['exit_code']==0 and not rec['timed_out']
    assert sha(src)==rec['source_sha256'] and sha(log)==rec['log_sha256']
    assert data['audit-001/'+name+'.lean']==src.read_bytes()
    assert data['audit-001/'+name+'.log']==log.read_bytes()
    assert data['audit-001/'+name+'.json']==(PUB/(name+'.json')).read_bytes()
    assert hb(data['audit-001/inventory.json'])==rec['inventory_sha256']
    ai=json.loads(data['audit-001/inventory.json'])
    assert {e['module'] for e in ai['modules']}==primary and ai['external_imports']==['Init']
    for e in ai['modules']:assert e['source_sha256']==sources[e['module']] and e['imports']==imports[e['module']]
    expected_source=WORK/'audit-001'/(name+'.lean');obj=expected_source.with_suffix('.olean')
    assert rec['command']==[boundary['lean']['path'],'-j1','-M12288','--root='+str(WORK/'audit-001'),'-o',str(obj),str(expected_source)]
    reports=re.findall(r'depends on axioms: \[([^]]*)\]',log.read_text())
    assert len(reports)==expected and 'sorryAx' not in log.read_text()
    assert 'warning:' not in log.read_text() and 'error:' not in log.read_text()
    axioms=set()
    for report in reports:axioms.update(x.strip() for x in report.split(','))
    assert axioms<={'propext','Classical.choice','Quot.sound'}
    assert src.read_text().count('#print axioms')==expected
    audits[name]={'reports':expected,'axioms':sorted(axioms),'warnings':0,'object_sha256':sha(obj),'source_sha256':sha(src),'log_sha256':sha(log)}
# Current generator receipts bind the unchanged inputs and generated source outputs.
gen=read(PUB/'generators.json')
assert gen['status']=='PASS_BYTE_EXACT'
for p,d in gen['inputs'].items():assert sha(p)==d
receipt={'status':'PASS_INDEPENDENT_CURRENT_SOURCE_OBJECT_AND_SAVED_LOG_REVIEW',
 'scope':'Read-only: current215 union modules, exact primary201 closure and Init boundary, current object/direct-dependency ledger, raw saved compilation/audit logs,107-member archive integrity, and unchanged204 baseline objects. No proof compilation or supplied script executed.',
 'result_sha256':sha(PUB/'result.json'),'archive_sha256':sha(archive),'archive_members':len(index),'compiled_objects_in_archive':0,
 'primary_modules':len(primary),'additional_legacy_modules':len(rows)-len(primary),'primary_warnings':warning_sum,
 'fresh_final_records':sum(v!='baseline' for v in origins.values()),'baseline_reused_records':sum(v=='baseline' for v in origins.values()),
 'baseline_objects_unchanged':len(baseline),'external_imports':sorted(external),'audits':audits,
 'compiler_sha256':result['compiler_sha256'],'Init_sha256':boundary['Init.olean']['sha256'],
 'findings':[], 'module_sources':sources,'module_objects':current_objects,'module_logs':logs,'origins':origins,
 'reviewer_sha256':sha(Path(__file__))}
(OUT/'review.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('module_sources','module_objects','module_logs','origins')},indent=2))
