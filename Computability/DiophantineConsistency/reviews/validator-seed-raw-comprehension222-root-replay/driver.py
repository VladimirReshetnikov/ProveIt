from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
P=Path(tempfile.mkdtemp(prefix='validator-seed-raw-comprehension222-root-'))
observations=[]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def rec(p):
    p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def pin(p,h=None):
    if isinstance(p,dict):h=p['sha256'];p=p['path']
    a=rec(p);need(h is None or a['sha256']==h,'hash '+str(p));observations.append(a);return a
def read(p):return json.loads(Path(p).read_text())
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def guard():need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
def imports(p):
    s=Path(p).read_text();out=[];i=depth=0
    while i<len(s):
        pair=s[i:i+2]
        if depth:
            if pair=='/-':depth+=1;i+=2
            elif pair=='-/':depth-=1;i+=2
            else:out.append('\n'if s[i]=='\n'else' ');i+=1
        elif pair=='/-':depth=1;i+=2
        elif pair=='--':
            while i<len(s)and s[i]!='\n':i+=1
        else:out.append(s[i]);i+=1
    need(depth==0,'balanced comments');s=''.join(out)
    initial=[]if re.search(r'^\s*prelude\s*$',s,re.M)else['Init']
    return list(dict.fromkeys(initial+[n for row in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M)for n in row.split()]))
state=dict(status='PREFLIGHT',private=str(P),records=[]);save(P/'state.json',state)
shutil.copyfile(__file__,P/'driver.py');print('PRIVATE '+str(P),flush=True)
try:
    guard()
    ap=V/'validator-seed-raw-comprehension222-replay.json'
    pin(ap,'e78586fcd4571a9efd18c7e908339b3f18dc901594371b77702896f8e2b09fe1');a=read(ap)
    pin(V/'validator-seed-raw-comprehension222-author.md','9721335981a637099a6d1cd8fb9a2511e8d98df23e08ba786d117d5922ffda88')
    need(a['status']=='PASS'and len(a['attempts'])==6,'author chronology')
    bundle=Path(a['bundle']);mf=bundle/'FILES.json';pin(mf,'bb7c3ca557ab41cc1c36944e6d2a62830e08a26e3d9f75f3ca9bddbd2c69d88b')
    rows=read(mf);need(len(rows)==76,'author evidence size')
    for x in rows:
        q=Path(x['path']);need(not q.is_absolute()and'..'not in q.parts,'bundle-relative evidence');pin(bundle/q,x['sha256'])
    cache=V/'validator-seed-raw-comprehension222-cache.json';pin(cache,'4f8bc557fe69b298526859717182a1d6e557fe8d934420fb0ac98e0c66343c24');d=read(cache)
    need(d==a['inputs'],'author inventory identity')
    need(d['counts']==dict(cached_modules=201,foundation=136,artifacts=609,external_boundaries=45),'scope')
    for k in ['compiler','manifest','toolchain']:pin(d[k],d[k+'_sha256'])
    for x in d['parent_receipts']+d['inherited_observations']:pin(x)
    mods={m['module']:m for m in d['modules']};ext={e['module']:e for e in d['external']}
    seen=set();active=set();boundary=set()
    def visit(n):
        if n not in mods:need(n in ext,'unknown boundary '+n);boundary.add(n);return
        if n in seen:return
        need(n not in active,'cycle '+n);active.add(n);m=mods[n]
        pin(m['source'],m['source_sha256']);actual=imports(m['source'])
        need(actual==m.get('actual_imports',m['imports']),'current header '+n)
        for child in actual:visit(child)
        for x in m['objects']:pin(x)
        active.remove(n);seen.add(n)
    visit('ZFCinPA.ValidatorSeedSourceBasis222')
    need(seen==set(mods)and boundary==set(ext),'exact reachable DAG')
    for x in ext.values():pin(x)
    for t in a['attempts']:
        original=Path(t['path']);saved=bundle/'attempts'/original.name
        pin(saved/'state.json',t['state_sha256']);s=read(saved/'state.json');need(s['status']==t['status'],'historical status')
        for row in s['completed']:
            pin(saved/Path(row['snapshot']).name,row['source_sha256'])
            pin(saved/Path(row['log']).name,row['log_sha256']);pin(saved/Path(row['timing']).name,row['timing_sha256'])
            need(row['command'][1:4]==['-M6000','-j1','-DElab.async=false'],'historical caps')
    need([t['status']for t in a['attempts']]==['FAIL']*5+['PASS'],'six-attempt chronology')
    lib=P/'lib';lib.mkdir()
    for m in mods.values():
        folder=lib/Path(*m['module'].split('.')[:-1]);folder.mkdir(parents=True,exist_ok=True)
        for x in m['objects']:(folder/Path(x['path']).name).symlink_to(Path(x['path']).resolve())
    paths=[str(lib),*d['lean_path'].split(':')[1:]]
    std=str(Path(d['compiler']).parent.parent/'lib/lean')
    if std not in paths:paths.append(std)
    providers=[]
    for m in [*mods.values(),*ext.values()]:
        expected=m['objects']if'objects'in m else[m]
        for ob in expected:
            rel=Path(*m['module'].split('.')[:-1])/Path(ob['path']).name
            first=next((Path(q)/rel for q in paths if(Path(q)/rel).is_file()),None)
            need(first is not None,'first artifact '+str(rel))
            providers.append(dict(module=m['module'],expected=ob,actual=pin(first,ob['sha256'])))
    need(len(providers)==654,'all first artifact providers')
    logs=P/'logs';logs.mkdir();sources=[]
    for ar in a['completed']:
        source=pin(ar['source'],ar['source_sha256']);snap=logs/Path(source['path']).name;shutil.copyfile(source['path'],snap)
        sources.append(dict(module=ar['module'],source=source,snapshot=rec(snap)))
    need(imports(sources[0]['source']['path'])==['Init','ZFCinPA.ValidatorSeedSourceBasis222'],'main imports')
    need(imports(sources[1]['source']['path'])==['Init',sources[0]['module']],'Checks imports')
    save(P/'providers.json',providers);save(P/'authentication.json',observations)
    inputs=dict(baseline_inventory=rec(cache),author=rec(ap),counts=d['counts'],compiler=rec(d['compiler']),LEAN_PATH=paths,
                sources=sources,providers=rec(P/'providers.json'),authentication=rec(P/'authentication.json'))
    save(P/'inputs.json',inputs);state.update(status='RUNNING',inputs=rec(P/'inputs.json'),driver=rec(P/'driver.py'));save(P/'state.json',state)
    env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
    for i,src in enumerate(sources):
        guard();pin(src['source']);pin(src['snapshot']);name=src['module'];out=lib/Path(*name.split('.')).with_suffix('.olean')
        out.parent.mkdir(parents=True,exist_ok=True);need(not out.exists()and not out.is_symlink(),'fresh output')
        log=logs/(name+'.log');timing=logs/(name+'.time');cmd=[d['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(out),src['source']['path']]
        print('START '+name,flush=True);start=time.monotonic()
        with log.open('w')as stream:
            code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=stream,stderr=subprocess.STDOUT).returncode
        row=dict(module=name,source=src['source'],snapshot=src['snapshot'],command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing))
        state['records'].append(row);save(P/'state.json',state)
        text=log.read_text();print(text,flush=True);need(code==0,'compiler '+name)
        need(not re.search(r'\b(?:warning|error|sorryAx)\b',text),'clean final log')
        rs=[list(x)for x in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)]
        need(len(rs)==(11 if i else 0),'report count')
        for _,axs in rs:need(set(re.findall(r'[A-Za-z][A-Za-z.]*',axs))<={'propext','Classical.choice','Quot.sound'},'standard axioms')
        need(out.is_file()and not out.is_symlink(),'regular output');row.update(object=rec(out),axiom_reports=rs)
        ar=a['completed'][i];pin(ar['object']);pin(ar['log'],ar['log_sha256'])
        need(row['object']['sha256']==ar['object']['sha256']and row['log']['sha256']==ar['log_sha256'],'author object/full-log equality')
        need(rs==ar['axiom_reports'],'complete report equality');row['author_object_and_full_log_equal']=True
        save(P/'state.json',state);pin(src['source']);guard();print('PASS '+name,flush=True)
    for x in list(observations):pin(x)
    state.update(status='PASS',observations=len(observations),distinct_paths=len({x['path']for x in observations}),final_free_bytes=shutil.disk_usage('/tmp').free)
    save(P/'state.json',state);print('PASS '+str(P),flush=True)
except BaseException as error:
    state.update(status='FAILED',failure=str(error));save(P/'state.json',state);raise
