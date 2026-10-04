#!/usr/bin/env python3
"""Independent article artifact archive/relocation replay; never executes mathematical code."""
import hashlib,json,os,pathlib,shutil,stat,subprocess,sys,zipfile
P=pathlib.Path; D=P('/workspace/shared/report66-release-tools-independent-review-20261004'); R=D/'article-candidate'; ORIGINAL=P('/workspace/shared/report66-bounded-certificates-counting-release-20261004')
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
pins=json.loads((D/'ARTICLE_TESTED_PINS.json').read_bytes())
for n,h in pins.items():assert sha((R/n).read_bytes())==h and sha((ORIGINAL/n).read_bytes())==h,n
readme=ORIGINAL/'README.md';assert sha(readme.read_bytes())=='ab6bd588c22385e51573f7873930c0bd352f3db01b6f22c1f14b5b675524dc13'
shutil.copy2(readme,R/'README.md')
def snapshot(root):
    result={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();o={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'type':stat.S_IFMT(s.st_mode)}
        if stat.S_ISREG(s.st_mode):o.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
        result[str(p.relative_to(root))]=o
    return result
checks=[]
def run(name,root,tool,args):
    before=snapshot(root)
    result=subprocess.run([sys.executable,'-I','-S','-B',str(root/'tools'/tool),*map(str,args)],cwd=D,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=480)
    (D/(name+'.stdout')).write_bytes(result.stdout)
    assert result.returncode==0,(name,result.stdout.decode(errors='replace')[-5000:]);assert snapshot(root)==before,(name,'changed source')
    checks.append({'name':name,'status':'PASS','source_preserved':True});print('PASS',name,flush=True)
    return json.loads(result.stdout)
initial=json.loads((D/'article-locked-replay/BUILD_RECEIPT.json').read_bytes());assert initial['status']=='PASS' and initial['packaged_pdf_match'] and initial['pdf_sha256']==pins['Report66.pdf'] and initial['page_count']==21
assert (D/'article-locked-replay/Report66.pdf').read_bytes()==(R/'Report66.pdf').read_bytes()
# Reconstruct system recorder union from every retained .fls, without trusting the generated union JSON.
def audit_union(folder):
    system=set();stages={}
    for label in ('format','compile-1','compile-2','compile-3'):
        p=folder/(label+'.fls');lines=p.read_text().splitlines();cwd=P(next(x[4:] for x in lines if x.startswith('PWD ')))
        localbase=cwd.parent if label=='format' else cwd
        ext=set()
        for line in lines:
            if line.startswith('INPUT '):
                raw=P(line[6:]);path=raw if raw.is_absolute() else cwd/raw
                if path==localbase or localbase in path.parents:continue
                path=path.resolve(strict=True)
                assert str(path).startswith(('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/','/var/lib/texmf/')),path
                ext.add(str(path))
        system|=ext;stages[label]=sorted(ext)
    for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
        system.add(str(P((folder/('map-'+name+'.stdout')).read_text().strip()).resolve(strict=True)))
    receipt=json.loads((folder/'BUILD_DEPENDENCIES.json').read_bytes());assert system==set(receipt['system_inputs'])
    for name,row in receipt['system_inputs'].items():data=P(name).read_bytes();assert row=={'bytes':len(data),'sha256':sha(data)}
    reported=json.loads((folder/'RECORDER_INPUT_UNION.json').read_bytes())
    assert {x['pass']:x['system_inputs'] for x in reported['passes']}==stages
    return {'system_input_count':len(system),'recorder_stages':{n:len(s) for n,s in stages.items()},'union_reconstructed_independently':True}
union1=audit_union(D/'article-locked-replay');checks.append({'name':'article-recorder-union-independent-reconstruction','status':'PASS',**union1})
manifest=D/'article-candidate-manifest.json';m=run('article-manifest-create',R,'release66.py',['manifest','--output',manifest]);shutil.copy2(manifest,R/'RELEASE_MANIFEST.json');mpin=sha(manifest.read_bytes());assert mpin==m['manifest_sha256']
run('article-verify',R,'release66.py',['verify','--manifest-sha256',mpin])
archives=[]
for n in (1,2):
    target=D/('article-archive-'+str(n)+'.zip');run('article-archive-'+str(n),R,'release66.py',['archive','--manifest-sha256',mpin,'--output',target]);archives.append(target)
assert archives[0].read_bytes()==archives[1].read_bytes();checks.append({'name':'article-archive-byte-equality','status':'PASS','sha256':sha(archives[0].read_bytes())})
with zipfile.ZipFile(archives[0]) as archive:
    info=archive.infolist();manifest_data=json.loads(manifest.read_bytes());assert archive.namelist()==['Report66/'+n for n in sorted([*manifest_data['files'],'RELEASE_MANIFEST.json'])]
    assert all(i.date_time==(2026,10,4,0,0,0) and i.create_system==3 and i.compress_type==zipfile.ZIP_DEFLATED for i in info)
    for i in info:
        n=i.filename.removeprefix('Report66/');assert archive.read(i)==(R/n).read_bytes()
        if n!='RELEASE_MANIFEST.json':assert stat.S_IMODE(i.external_attr>>16)==manifest_data['files'][n]['mode']
checks.append({'name':'article-zip-independent-inventory-metadata-bytes','status':'PASS'})
extract=D/'article-extracted';run('article-extract',R,'release66.py',['extract','--archive',archives[0],'--output-dir',extract,'--manifest-sha256',mpin]);run('article-relocated-verify',extract,'release66.py',['verify','--manifest-sha256',mpin])
first=snapshot(R);second=snapshot(extract)
assert first.keys()==second.keys()
for name in first:
    if name not in ('.','RELEASE_MANIFEST.json'):assert first[name]==second[name],name
checks.append({'name':'article-extraction-independent-metadata-oracle','status':'PASS'})
replay=D/'article-relocated-locked-replay';result=run('article-relocated-locked-replay',extract,'build_report66.py',['--output-dir',replay,'--pins-sha',pins['manuscript/MANUSCRIPT_PINS.json'],'--dependency-lock-sha',pins['tools/BUILD_DEPENDENCIES_LOCK.json'],'--require-packaged-match'])
assert result['status']=='PASS' and result['packaged_pdf_match'] and result['page_count']==21
assert (replay/'Report66.pdf').read_bytes()==(D/'article-locked-replay/Report66.pdf').read_bytes()==(R/'Report66.pdf').read_bytes()
assert (replay/'BUILD_DEPENDENCIES.json').read_bytes()==(R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
assert audit_union(replay)==union1
checks.append({'name':'article-relocated-independent-pdf-lock-union-oracles','status':'PASS'})
for n,h in pins.items():assert sha((ORIGINAL/n).read_bytes())==h,n
receipt={'status':'PASS','scope':'Full final article candidate, not final later-assembled release seal; byte-exact presentation replay only, not mathematical execution or theorem verification','checks':checks,'check_count':len(checks),'article_pins':pins,'reviewed_readme_sha256':sha(readme.read_bytes()),'candidate_manifest_sha256':mpin,'candidate_archive_sha256':sha(archives[0].read_bytes()),'initial_build_receipt':initial,'relocated_build_receipt':result,'recorder_union':union1}
save(D/'INDEPENDENT_ARTICLE_RESULTS.json',receipt)
print(json.dumps({'status':'PASS','check_count':len(checks)}),flush=True)
