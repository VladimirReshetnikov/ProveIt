#!/usr/bin/env python3
"""Fresh report-owned static TeX builder. Never executes scientific source files."""
import argparse,hashlib,json,re,stat,subprocess
from pathlib import Path
EPOCH='1791072000'
FILES=('Report65.tex','clock.tex','native.tex','normalization.tex','scope.tex')
SYSTEM=('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/')
def require(v,s):
    if not v: raise ValueError(s)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def encoded(x): return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def write(p,b):
    with p.open('xb') as f: f.write(b)
def regular(p):
    require(not p.is_symlink() and p.is_file(),'Not a regular file: '+str(p))
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--draft',action='store_true',help='Explicit unsealed authoring mode')
    ap.add_argument('--manifest-sha256',help='Expected sealed-release manifest digest')
    ap.add_argument('--dependency-lock',type=Path)
    ap.add_argument('--dependency-lock-sha256')
    a=ap.parse_args(); root=a.root.absolute(); out=a.output.absolute()
    require(root.resolve(strict=True)==root,'Root must be canonical without symlinks')
    require(not a.draft or not a.manifest_sha256,'Draft and sealed modes are exclusive')
    require(a.draft or a.manifest_sha256,'Choose explicit draft mode or give a manifest digest')
    def inventory():
        rows={}
        for p in sorted(root.rglob('*')):
            require(not p.is_symlink(),'Source symlink rejected')
            st=p.stat();require(stat.S_ISREG(st.st_mode) or stat.S_ISDIR(st.st_mode),'Special source file rejected')
            if p.is_file():rows[p.relative_to(root).as_posix()]={'sha256':digest(p),'bytes':st.st_size,'mode':stat.S_IMODE(st.st_mode),'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}
        return rows
    before=inventory()
    if a.manifest_sha256:
        mp=root/'MANIFEST.json';regular(mp);require(digest(mp)==a.manifest_sha256,'Manifest digest mismatch')
        manifest=json.loads(mp.read_text());require(manifest.get('schema')=='report65-release-v1','Manifest schema mismatch')
        require(set(before)==set(manifest['files'])|{'MANIFEST.json'},'Sealed file set mismatch')
        for rel,row in manifest['files'].items():
            require(all(before[rel][k]==row[k] for k in ('sha256','bytes','mode')),'Sealed file mismatch '+rel)
        require(a.dependency_lock and a.dependency_lock_sha256,'Sealed builds require the dependency lock')
    else:
        require(not (root/'MANIFEST.json').exists(),'Draft mode refuses a sealed release')
    require(not out.exists(),'Output already exists')
    require(root!=out and root not in out.parents and out not in root.parents,'Output overlaps release')
    require(out.parent.resolve(strict=True)==out.parent,'Output parent contains a symlink')
    inp=root/'manuscript'; texts={}
    for name in FILES:
        p=inp/name; regular(p); texts[name]=p.read_bytes()
    srcpins={n:hashlib.sha256(v).hexdigest() for n,v in texts.items()}
    flat=texts['Report65.tex'].decode()
    for name in FILES[1:]:
        tag='\\input{manuscript/'+name+'}'
        require(flat.count(tag)==1,'Unexpected manuscript include')
        flat=flat.replace(tag,texts[name].decode())
    require('\\input' not in flat and '\\include' not in flat,'Unresolved TeX include')
    require(not re.search(r'\\(?:write18|openin|openout|read|immediate|usepackage\s*\{shellesc)',flat),'Unsafe TeX primitive')
    flat=flat.replace('\\begin{document}','\\pdfinfoomitdate=1\n\\pdftrailerid{}\n\\pdfsuppressptexinfo=15\n\\begin{document}',1)
    executables={}
    for name in ('pdftex','pdflatex','kpsewhich','pdftotext','pdfinfo'):
        p=Path('/usr/bin')/name
        require(p.is_file(),'Missing system executable '+name)
        executables[name]={'resolved':str(p.resolve()),'sha256':digest(p),'bytes':p.stat().st_size}
    lock=None
    if a.dependency_lock:
        require(a.dependency_lock_sha256 and digest(a.dependency_lock)==a.dependency_lock_sha256,'Dependency lock digest mismatch')
        lock=json.loads(a.dependency_lock.read_text())
        require(lock['executables']==executables,'Executable lock mismatch')
        for p,row in lock['system_inputs'].items():
            q=Path(p);require(any(p.startswith(s) for s in SYSTEM),'Invalid locked system path')
            require(q.is_file() and digest(q)==row['sha256'] and q.stat().st_size==row['bytes'],'Changed locked system input '+p)
    else:
        require(not a.dependency_lock_sha256,'Digest without dependency lock')
    out.mkdir(mode=0o700);work=out/'work';cache=out/'cache';home=out/'home'
    for p in (work,cache,home):p.mkdir()
    write(work/'Report65.tex',flat.encode())
    env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC','HOME':str(home),
         'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1','TEXMF':'{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
         'TEXMFVAR':str(cache),'TEXMFCONFIG':str(cache),'TEXMFHOME':str(home),'TEXFORMATS':str(cache),
         'openin_any':'p','openout_any':'p','shell_escape':'f','MKTEXPK':'0','MKTEXTFM':'0','MKTEXMF':'0'}
    observed={}
    def system(p):
        p=p.resolve(strict=True);s=str(p)
        require(any(s.startswith(t) for t in SYSTEM),'Unexpected external TeX input '+s)
        row={'bytes':p.stat().st_size,'sha256':digest(p)}
        require(s not in observed or observed[s]==row,'System input changed')
        if lock:require(lock['system_inputs'].get(s)==row,'Unpinned TeX input '+s)
        observed[s]=row;return p.read_bytes()
    def record(p,base,label):
        data=p.read_bytes();write(out/(label+'.fls'),data)
        for line in data.decode().splitlines():
            if line.startswith('INPUT '):
                q=Path(line[6:]);q=(q if q.is_absolute() else base/q).resolve(strict=True)
                if out not in q.parents:system(q)
    def run(argv,cwd,label):
        name=Path(argv[0]).name
        require(digest(Path(argv[0]))==executables[name]['sha256'],'Executable changed')
        r=subprocess.run(argv,cwd=cwd,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=240)
        write(out/(label+'.stdout'),r.stdout)
        require(r.returncode==0,'Command failed '+label+'\n'+r.stdout.decode(errors='replace')[-6000:])
        return r.stdout
    run(['/usr/bin/pdftex','-ini','-etex','-no-shell-escape','-recorder','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,'format')
    record(cache/'pdflatex.fls',cache,'format')
    maps=[]
    for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
        paths=run(['/usr/bin/kpsewhich',name],work,'map-'+name).decode().strip().splitlines()
        require(len(paths)==1 and Path(paths[0]).is_absolute(),'Ambiguous font map')
        maps.append(system(Path(paths[0])))
    write(cache/'pdftex.map',b'\n'.join(maps)+b'\n');env['TEXFONTMAPS']=str(cache)+':'
    for i in range(1,4):
        label='compile-'+str(i)
        stdout=run(['/usr/bin/pdflatex','-no-shell-escape','-recorder','-halt-on-error','-interaction=nonstopmode','-file-line-error','Report65.tex'],work,label)
        record(work/'Report65.fls',work,label)
    warnings=[x for x in (b'Overfull \\hbox',b'Overfull \\vbox',b'undefined references',b'undefined citations',b'Rerun to get cross-references right',b'Label(s) may have changed') if x in stdout]
    if lock:require(observed==lock['system_inputs'],'Executed system input union differs')
    run(['/usr/bin/pdftotext','-layout','Report65.pdf','Report65.txt'],work,'pdftotext')
    run(['/usr/bin/pdfinfo','Report65.pdf'],work,'pdfinfo')
    for name in ('Report65.pdf','Report65.tex','Report65.txt','Report65.log'):write(out/name,(work/name).read_bytes())
    write(out/'BUILD_DEPENDENCIES_LOCK.json',encoded({'schema':'report65-build-lock-v1','executables':executables,'system_inputs':observed}))
    require(srcpins=={n:digest(inp/n) for n in FILES},'Manuscript changed during build')
    require(before==inventory(),'Source files or metadata changed during build')
    receipt={'schema':'report65-build-v1','source_sha256':srcpins,'pdf_sha256':digest(out/'Report65.pdf'),'flat_tex_sha256':digest(out/'Report65.tex'),'dependency_lock_sha256':digest(out/'BUILD_DEPENDENCIES_LOCK.json'),'warnings':[x.decode() for x in warnings],'system_input_count':len(observed),'scientific_code_executed':False}
    write(out/'BUILD.json',encoded(receipt));print(json.dumps(receipt,indent=2))
    require(not warnings,'Layout warnings require correction')
if __name__=='__main__':main()
