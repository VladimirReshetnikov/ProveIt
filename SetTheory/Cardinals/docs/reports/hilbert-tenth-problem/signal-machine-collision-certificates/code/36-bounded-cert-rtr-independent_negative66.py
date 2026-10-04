#!/usr/bin/env python3
"""Additional independently authored refusal-path tests, all on inert copies."""
import copy,hashlib,json,os,pathlib,shutil,stat,subprocess,sys,zipfile
P=pathlib.Path;D=P('/workspace/shared/report66-release-tools-independent-review-20261004');W=D/'additional-tests';W.mkdir();S=D/'test-work-v2/fixture';results=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
manifest=(S/'RELEASE_MANIFEST.json').read_bytes();mpin=sha(manifest);pins=sha((S/'manuscript/MANUSCRIPT_PINS.json').read_bytes());lockpin=sha((S/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())
def snap(r):
    out={}
    for p in [r,*sorted(r.rglob('*'))]:
        st=p.lstat();row={'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns,'type':stat.S_IFMT(st.st_mode),'nlink':st.st_nlink}
        if stat.S_ISREG(st.st_mode):row['sha256']=sha(p.read_bytes())
        elif stat.S_ISLNK(st.st_mode):row['link']=os.readlink(p)
        out[str(p.relative_to(r))]=row
    return out

def run(name,tool,args,root=S,flags=None,absent=None):
    before=snap(root);r=subprocess.run([sys.executable,*(flags or ['-I','-S','-B']),str(root/'tools'/tool),*map(str,args)],cwd=W,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,stdin=subprocess.DEVNULL,timeout=120)
    (D/('extra-'+name+'.stdout')).write_bytes(r.stdout);assert r.returncode!=0,(name,r.stdout);assert before==snap(root),(name,'mutated source')
    if absent is not None:assert not os.path.lexists(absent)
    results.append({'name':name,'status':'PASS','exit':r.returncode,'source_preserved':True,'no_output_created':absent is not None});print('PASS',name,flush=True)
for n in ('release66.py','build_report66.py'):
    args=['check-inputs'] if n=='release66.py' else ['--pins-sha',pins,'--dependency-lock-sha',lockpin,'--output-dir',W/('optimized-'+n)]
    run('reject-optimized-'+n,n,args,flags=['-I','-S','-B','-O'])
for name,mutation in [('tampered-helper',lambda r:(r/'tools/release66.py').write_bytes((r/'tools/release66.py').read_bytes()+b'\n')),('symlink-helper',lambda r:((r/'tools/release66.py').rename(r/'tools/helper-original.py'),(r/'tools/release66.py').symlink_to(r/'tools/helper-original.py'))),('hardlinked-helper',lambda r:os.link(r/'tools/release66.py',r/'tools/helper-link.py'))]:
    r=W/name;shutil.copytree(S,r,copy_function=shutil.copy2);mutation(r);out=W/(name+'-output');run('reject-'+name,'build_report66.py',['--pins-sha',pins,'--dependency-lock-sha',lockpin,'--output-dir',out],root=r,absent=out)
archive=D/'test-work-v2/archive-1.zip';al=W/'linked-archive.zip';al.symlink_to(archive)
out=W/'linked-archive-output';run('reject-symlink-archive','release66.py',['extract','--archive',al,'--output-dir',out,'--manifest-sha256',mpin],absent=out)
copyarchive=W/'copy-archive.zip';shutil.copy2(archive,copyarchive);os.link(copyarchive,W/'hardlink-archive.zip');out=W/'hardlink-output';run('reject-hardlinked-archive','release66.py',['extract','--archive',copyarchive,'--output-dir',out,'--manifest-sha256',mpin],absent=out)
with zipfile.ZipFile(archive) as z:original=[(copy.copy(i),z.read(i)) for i in z.infolist()]
variants={
 'duplicate-json':b'{"format":"Report66 release manifest v1","format":"Report66 release manifest v1","files":{},"directories":{}}\n',
 'manifest-directory-collision':enc({'format':'Report66 release manifest v1','files':{'RELEASE_MANIFEST.json/x':{'mode':420,'mtime_ns':1,'bytes':0,'sha256':sha(b'')}},'directories':{'RELEASE_MANIFEST.json':{'mode':493,'mtime_ns':1}}}),
 'manifest-absolute-path':enc({'format':'Report66 release manifest v1','files':{'/escape':{'mode':420,'mtime_ns':1,'bytes':0,'sha256':sha(b'')}},'directories':{}}),
 'manifest-extra-empty-dir':enc({'format':'Report66 release manifest v1','files':{},'directories':{'empty':{'mode':493,'mtime_ns':1}}}),
 'manifest-wrong-schema':enc({'format':'Report66 release manifest v1','files':{},'directories':{},'additional':True}),
}
for name,data in variants.items():
    a=W/(name+'.zip')
    with zipfile.ZipFile(a,'w') as z:
        for info,old in original:z.writestr(info,data if info.filename=='Report66/RELEASE_MANIFEST.json' else old)
    out=W/(name+'-output');run('reject-archive-'+name,'release66.py',['extract','--archive',a,'--output-dir',out,'--manifest-sha256',sha(data)],absent=out)
# Manifest entry itself must still be a regular Unix entry, even though its mode is not independently pinned.
a=W/'manifest-symlink-entry.zip'
with zipfile.ZipFile(a,'w') as z:
    for info,data in original:
        info=copy.copy(info)
        if info.filename=='Report66/RELEASE_MANIFEST.json':info.external_attr=(stat.S_IFLNK|0o777)<<16
        z.writestr(info,data)
out=W/'manifest-symlink-output';run('reject-manifest-symlink-entry','release66.py',['extract','--archive',a,'--output-dir',out,'--manifest-sha256',mpin],absent=out)
(D/'INDEPENDENT_ADDITIONAL_RESULTS.json').write_bytes(enc({'status':'PASS','test_count':len(results),'tests':results,'scope':'Additional release/build rejection paths only; no mathematical code executed'}));print('TOTAL',len(results))
