#!/usr/bin/env python3
"""Build the pinned Report58 manuscript with a fresh system-only TeX cache.
Run with python3 -I -S -B. Output must be a new canonical external directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent.parent
EPOCH='1791072000'
SOURCE_SHA256='cc1ffd8ce344dcf45d89d40d4ceadff8eb2decc513c595bdf7b4462465864e89'
SYSTEM_ROOTS=('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/','/var/lib/texmf/')

def need(ok,message):
    if not ok:raise ValueError(message)

def digest(raw):return hashlib.sha256(raw).hexdigest()
def sha(p):return digest(p.read_bytes())
def encode(v):return json.dumps(v,indent=2,sort_keys=True)+'\n'

def regular(p):
    st=p.lstat()
    need(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'Regular unlinked file required: '+str(p))
    return p.read_bytes()

def new_output(raw):
    need(raw.startswith('/') and not raw.startswith('//'),'Output must be canonical absolute path')
    p=Path(raw)
    need(str(p)==raw and all(x not in ('.','..') for x in raw.split('/')),'Noncanonical output path')
    for q in reversed([p,*p.parents]):
        if os.path.lexists(q):
            st=q.lstat()
            need(not stat.S_ISLNK(st.st_mode),'Symlink path component rejected')
            need(q==p or stat.S_ISDIR(st.st_mode),'Output ancestor is not a directory')
        else:need(q==p,'Output parent must already exist')
    need(not os.path.lexists(p),'Output must not already exist')
    need(p!=ROOT and ROOT not in p.parents and p not in ROOT.parents,'Output must be external to the release')
    return p

def run(argv,cwd,env,timeout=120):
    proc=subprocess.run(argv,cwd=cwd,env=env,stdin=subprocess.DEVNULL,
       stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=timeout)
    return proc

def main():
    need(sys.flags.isolated==1 and sys.flags.no_site==1 and sys.dont_write_bytecode and sys.flags.optimize==0,
         'Invoke with python3 -I -S -B and no optimization')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',required=True)
    ap.add_argument('--render-dpi',type=int,default=120)
    ap.add_argument('--draft',action='store_true',help='Permit a new reviewed manuscript render before replacing the packaged PDF')
    args=ap.parse_args()
    need(72<=args.render_dpi<=200,'Render DPI must be 72 through 200')
    source=regular(ROOT/'Report58.tex')
    need(digest(source)==SOURCE_SHA256,'Manuscript hash differs from reviewed build input')
    out=new_output(args.output_dir)
    executables={}
    for name in ('pdftex','pdflatex','kpsewhich','pdftotext','pdftoppm','pdfinfo'):
        p=(Path('/usr/bin')/name).resolve()
        need(p.is_file(),'Missing installed executable: '+name)
        executables[name]={'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
    out.mkdir(mode=0o700)
    try:
        with tempfile.TemporaryDirectory(prefix='report58-build-') as raw:
            work=Path(raw);(work/'Report58.tex').write_bytes(source)
            cache=work/'tex-cache';cache.mkdir();home=work/'home';home.mkdir()
            env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC','HOME':str(home),
              'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1',
              'TEXMF':'{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
              'TEXMFVAR':str(cache),'TEXMFCONFIG':str(cache),'TEXMFHOME':str(home),
              'TEXFORMATS':str(cache)+':','openin_any':'p','openout_any':'p','shell_escape':'f',
              'MKTEXPK':'0','MKTEXTFM':'0','MKTEXMF':'0'}
            fmt=run(['/usr/bin/pdftex','-ini','-etex','-no-shell-escape','-recorder','-interaction=nonstopmode',
               '-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env)
            (out/'format-build.log').write_text(fmt.stdout)
            need(fmt.returncode==0,'Fresh TeX format build failed')
            maps=[];system={}
            def system_file(path):
                p=path.resolve()
                need(any(str(p).startswith(prefix) for prefix in SYSTEM_ROOTS),'Unexpected external TeX input: '+str(p))
                raw=p.read_bytes()
                system[str(p)]={'bytes':len(raw),'sha256':digest(raw)}
                return raw
            for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
                found=run(['/usr/bin/kpsewhich',name],work,env,30)
                need(found.returncode==0 and found.stdout.strip(),'Missing system font map: '+name)
                maps.append(system_file(Path(found.stdout.strip())))
            (cache/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n');env['TEXFONTMAPS']=str(cache)+':'
            logs=[]
            for n in range(3):
                build=run(['/usr/bin/pdflatex','-no-shell-escape','-recorder','-halt-on-error',
                   '-interaction=nonstopmode','-file-line-error','Report58.tex'],work,env)
                logs.append(build.stdout);(out/('compile-%d.log'%(n+1))).write_text(build.stdout)
                need(build.returncode==0,'LaTeX build failed; inspect compile log')
            bad=('Overfull \\hbox','Overfull \\vbox','undefined references','undefined citations',
                 'Rerun to get cross-references right','Label(s) may have changed','rerunfilecheck Warning')
            need(not any(x in logs[-1] for x in bad),'Final layout or reference warning')
            for recorder,base in ((cache/'pdflatex.fls',cache),(work/'Report58.fls',work)):
                for line in recorder.read_text().splitlines():
                    if line.startswith('INPUT '):
                        p=Path(line[6:]);p=p if p.is_absolute() else base/p;p=p.resolve()
                        if p!=work and work not in p.parents:system_file(p)
            pdf=(work/'Report58.pdf').read_bytes();need(pdf.startswith(b'%PDF-'),'Missing PDF signature')
            matches=(ROOT/'Report58.pdf').exists() and pdf==regular(ROOT/'Report58.pdf')
            if not args.draft:need(matches,'Clean PDF differs from packaged PDF')
            need(regular(ROOT/'Report58.tex')==source,'Manuscript changed during build')
            (out/'Report58.pdf').write_bytes(pdf);(out/'Report58.log').write_bytes((work/'Report58.log').read_bytes())
            p=run(['/usr/bin/pdftotext','-layout',str(out/'Report58.pdf'),str(out/'Report58.txt')],work,env)
            need(p.returncode==0,'Text extraction failed')
            p=run(['/usr/bin/pdfinfo',str(out/'Report58.pdf')],work,env);need(p.returncode==0,'PDF info failed')
            (out/'pdfinfo.txt').write_text(p.stdout)
            pages=out/'pages';pages.mkdir()
            p=run(['/usr/bin/pdftoppm','-r',str(args.render_dpi),'-png',str(out/'Report58.pdf'),str(pages/'page')],work,env)
            need(p.returncode==0,'PDF render failed')
            deps={'executables':executables,'system_inputs':system,'source_date_epoch':int(EPOCH),
              'scope':'Installed TeX recorder and font-map inputs plus executable files; dynamically linked libraries are not included.'}
            (out/'BUILD_DEPENDENCIES.json').write_text(encode(deps))
            files={str(p.relative_to(out)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(out.rglob('*')) if p.is_file()}
            receipt={'source_sha256':digest(source),'pdf_sha256':digest(pdf),'source_date_epoch':int(EPOCH),
              'render_dpi':args.render_dpi,'render_pages':len(list(pages.glob('page-*.png'))),'files':files,
              'fresh_format_cache':True,'minimal_environment':True,'shell_escape':False,'source_preserved':True,
              'packaged_pdf_exact_match':matches,
              'scope':'Deterministic typesetting and rendering only; no scientific programs executed.'}
            (out/'BUILD_RECEIPT.json').write_text(encode(receipt))
            print(encode({k:receipt[k] for k in ('source_sha256','pdf_sha256','render_pages')}))
    except BaseException as e:
        (out/'BUILD_FAILURE.json').write_text(encode({'status':'FAIL','error':str(e)}))
        raise

if __name__=='__main__':
    try:main()
    except (ValueError,OSError,subprocess.SubprocessError) as e:
        print('BUILD REFUSED: '+str(e),file=sys.stderr)
        raise SystemExit(2)
