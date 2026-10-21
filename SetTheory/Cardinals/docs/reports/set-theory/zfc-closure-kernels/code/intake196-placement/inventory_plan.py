"""Own read-only Git/ZIP inventory. No delivered code or checksum manifest is executed/validated."""
from pathlib import Path, PurePosixPath
from collections import defaultdict, Counter
import hashlib, io, json, re, subprocess, zipfile

OUT=Path('/tmp/zfc-intake196/procedure')
HOST='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
REF='58615b1aa1e93782d5152a2233332c14f664bd8f'
def git(*args):return subprocess.check_output(['git',*args])
def text(*args):return git(*args).decode()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def tree(ref):
    d={}
    for row in git('ls-tree','-r','-z',ref).split(b'\0'):
        if row:
            info,p=row.split(b'\t',1);mode,typ,h=info.decode().split()
            if typ=='blob':d[p.decode()]=h
    return d
def put(name,data):
    p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True)
    s=json.dumps(data,indent=2,ensure_ascii=False)+'\n'
    if p.exists():assert p.read_text()==s,('Different existing output',str(p))
    else:p.write_text(s)
def package(ref,name):
    raw=git('show',ref+':docs/incoming/'+name)
    z=zipfile.ZipFile(io.BytesIO(raw));rows=[]
    for i in z.infolist():
        if i.is_dir():continue
        path=PurePosixPath(i.filename)
        assert not path.is_absolute()and '..'not in path.parts
        assert ((i.external_attr>>16)&0o170000)!=0o120000,'Symlink member'
        b=z.read(i);rows.append(dict(member=i.filename,relative='/'.join(path.parts[1:]),blob=blob(b),bytes=len(b),_content=b))
    assert len({r['member']for r in rows})==len(rows)
    return dict(arrival=text('rev-parse',ref).strip(),archive='docs/incoming/'+name,archive_blob=blob(raw),archive_bytes=len(raw),members=rows)

current=tree(REF);byblob=defaultdict(list)
for p,h in current.items():byblob[h].append(p)
# All reachable historical blob identities, without expanding or running payloads.
historical=defaultdict(list)
for row in git('rev-list','--objects','--all').splitlines():
    h,sep,p=row.partition(b' ')
    if sep:historical[h.decode()].append(p.decode(errors='replace'))

specs=[(157,'scanner','d3d6b8c14e','ZFC_217_Scanner_Source_Research_2026-10-21.zip'),(158,'research','d3d6b8c14e','zfc217-research-2026-10-21.zip')]
pins={157:'704b87442afbd571833a628cd558f1d207fd8b2f',158:'704b87442afbd571833a628cd558f1d207fd8b2f'}
archive_only={}
for number,slug,arrival,name in specs:
    archive_only[number]={d['relative'] for d in package(arrival,name)['members'] if d['relative']=='README.md' or PurePosixPath(d['relative']).suffix.lower() in {'.tex','.pdf'}}

archive_only[157].discard('formalism/seed/seed_calibration.tex')
archive_only[158].discard('research/formalism/seed217_lemma.tex')
archive_only[158].discard('research/formalism/formalism_research_note.tex')

code_ext={'.py','.sh','.ps1','.wl','.wls','.lean','.cpp','.c','.h','.v','.tex'}
short={'research':'res','encoding':'enc','verification':'ver','portable':'port','reference_results':'ref','replay_logs':'logs','exploratory':'exp','receipts':'rec','scripts':'src','local_folds':'folds','licenses':'lic','specialization_audit':'spec','experiments':'exp','release_replay':'replay','sections':'sec','construction':'build','certificates':'cert','machine':'mach','quick_replay':'quick','isolated_default_logs':'default-logs','release_full':'full','release_independent_quick':'quick','reference_results':'ref','research218_encoding':'enc','research218_baseline_audit':'base','research218_source':'src','k223_merged_runtime_audit':'runtime223','latest219_baseline':'base219','evidence':'ev','checks':'chk','dominated':'dom'}
introductions={};history_zip={};target_used={};batch_blob={};sources=[]
def introduced(path,h):
    if(path,h)in introductions:return introductions[path,h]
    log=text('log','--all','--format=%H\t%s','--find-object='+h,'--',path).splitlines()
    choices=[]
    for line in log:
        c,subject=line.split('\t',1)
        out=text('ls-tree',c,'--',path).strip()
        if out and out.split()[2]==h:
            choices.append(dict(commit=c,path=path,blob=h,subject=subject,placement=bool(re.search(r'^(Place |Unpack, classify|Unpack |Import )',subject))))
    assert choices,('No original introduction',path,h)
    v=next((c for c in choices if c['placement']),choices[-1]);introductions[path,h]=v;return v
def history_binding(h,preferred=None):
    if h in history_zip:return history_zip[h]
    log=text('log','--all','--format=%H\t%s','--find-object='+h,'--','docs/incoming').splitlines()
    candidates=[]
    for line in log:
        c,subject=line.split('\t',1)
        for row in text('ls-tree','-r',c,'--','docs/incoming').splitlines():
            info,path=row.split('\t',1)
            if info.split()[2]==h:candidates.append(dict(commit=c,path=path,blob=h,subject=subject))
    assert candidates,('No history ZIP binding',h,preferred)
    v=next((c for c in candidates if c['subject'].startswith('New ')),candidates[-1]);history_zip[h]=v;return v

for number,slug,arrival,name in specs:
    p=package(arrival,name);members=[]
    for d in p['members']:
        rel=d['relative'];h=d['blob'];q={k:v for k,v in d.items()if k!='_content'};q['source']=number
        if rel in archive_only[number]:q.update(role='archive-only',reason='Main article/input fragment/PDF or delivery README; retained in arrival archive.')
        elif rel.endswith('.zip') and (h in historical or h in byblob):
            q.update(role='history-alias',history=history_binding(h,rel),reason='Exact vendored predecessor archive recoverable from committed arrival.')
        else:
            paths=[x for x in byblob.get(h,[])if not x.startswith('docs/incoming/')]
            if paths:
                path=min(paths,key=lambda x:(not x.startswith(HOST+'/'),len(x),x))
                q.update(role='existing-alias',target=path,original_introduction=introduced(path,h),current_ref=REF)
            elif h in batch_blob:
                q.update(role='batch-alias',target=batch_blob[h]['target'],target_source=batch_blob[h]['source'])
            else:
                pp=PurePosixPath(rel);base=pp.name.lower();ext=pp.suffix.lower()
                role='root'if(ext=='.md'or base.startswith(('readme','license','notice','attribution'))or 'license'in base)else'code'if(ext in code_ext or base=='makefile')else'data'
                parts=[short.get(x,x)for x in pp.parts];leaf=f'{number}-{slug}-'+'-'.join(parts)
                target=HOST+'/'+(''if role=='root'else role+'/')+leaf
                assert target not in current and target not in target_used,target
                if len('C:/ProveIt/'+target)>=200:
                    leaf=f'{number}-{slug}-'+pp.stem[:65]+'-'+h[:10]+pp.suffix
                    target=HOST+'/'+(''if role=='root'else role+'/')+leaf
                assert len('C:/ProveIt/'+target)<200,(len('C:/ProveIt/'+target),target)
                assert target not in current and target not in target_used,target
                q.update(role='new',destination_role=role,target=target,windows_length=len('C:/ProveIt/'+target))
                if h in historical:q['historical_blob_candidates']=historical[h]
                target_used[target]=h;batch_blob[h]=q
        members.append(q)
    sources.append({**{k:v for k,v in p.items()if k!='members'},'source':number,'slug':slug,'reviewed_snapshot':pins[number],'snapshot_note':'Inspected repository snapshot stated in each delivery README; inherited parent/source identities are separately retained.','members':members,'counts':dict(Counter(q['role']for q in members))})

allmembers=[q for s in sources for q in s['members']]
assert len(allmembers)==343
new=[q for q in allmembers if q['role']=='new']
unresolved=[q for q in new if q.get('historical_blob_candidates')]
put('placement-plan.json',dict(status='SOURCE_ONLY_PLACEMENT_PLAN',ref=REF,batch=196,host=HOST,manuscript_order=[157,158],source_count_after=158,report_count_after=290,sources=sources,counts=dict(Counter(q['role']for q in allmembers)),new_destination_roles=dict(Counter(q['destination_role']for q in new)),maximum_new_windows_length=max(q['windows_length']for q in new),historical_unresolved=[dict(source=q['source'],member=q['member'],blob=q['blob'],candidates=q['historical_blob_candidates'])for q in unresolved],candidate_execution=False,checksum_manifest_validation=False,notes=['Fresh root-owned extraction/copy/staging required; this script writes metadata only.','Main report, TeX inputs, PDF, and root delivery README are archive-only; all ancillary Markdown, proof scripts and other payloads are retained or aliased.','All nested README/audit/provenance Markdown and licenses retained at report root unless exact existing alias.','Only the scanner/source and zfc217-research archives fromd3d6b8c14e are in this batch. Sources157–158 continue the156-source host; no new candidate is accepted by placement.','Explicitly force-add mapped logs/nested ZIPs if ignored; do not alter ignore policy.','Existing aliases bind both current object identity and an original introduction tree; history ZIP aliases bind the exact arrival tree.']))
print(json.dumps(dict(ref=REF,total=len(allmembers),counts=dict(Counter(q['role']for q in allmembers)),per_source=[dict(source=s['source'],counts=s['counts'])for s in sources],new_roles=dict(Counter(q['destination_role']for q in new)),max_windows_length=max(q['windows_length']for q in new),historical_unresolved=len(unresolved)),indent=2))
