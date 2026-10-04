#!/usr/bin/env python3
"""Isolated deterministic typesetting and all-page rendering; execute no scientific source.
Invoke: python3 -I -S -B tools/build_report59.py --output-dir /fresh/external/path
"""
import argparse,hashlib,json,os,stat,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
EPOCH='1791072000'
SYSTEM_ROOTS=('/usr/share/texlive/','/usr/share/texmf/','/etc/texmf/','/var/lib/texmf/')

def require(test,message):
    if not test: raise ValueError(message)

def sha(data): return hashlib.sha256(data).hexdigest()
def encode(x):return json.dumps(x,indent=2,sort_keys=True)+'\n'
def file_bytes(p):
    st=p.lstat();require(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'Expected regular single-link file: '+str(p));return p.read_bytes()
def snapshot():
    files={}
    for directory in ('science','independent-audit','manuscript','dependencies','real-input','real-input-audit','real-input-dependencies'):
        base=ROOT/directory
        if not base.exists():continue
        for p in sorted(base.rglob('*')):
            require(not p.is_symlink(),'Symlink forbidden in inputs: '+str(p))
            if p.is_file(): files[str(p.relative_to(ROOT))]=sha(file_bytes(p))
    return files

def destination(raw):
    require(raw.startswith('/') and not raw.startswith('//'),'Canonical absolute output path required')
    p=Path(raw);require(str(p)==raw and all(x not in ('.','..') for x in raw.split('/')),'Noncanonical output path')
    for q in reversed([p,*p.parents]):
        if os.path.lexists(q):
            st=q.lstat();require(not stat.S_ISLNK(st.st_mode),'Symlink output component')
            require(q==p or stat.S_ISDIR(st.st_mode),'Output ancestor must be a directory')
        else:require(q==p,'Output parent must already exist')
    require(not os.path.lexists(p),'Output must be new')
    require(p!=ROOT and ROOT not in p.parents and p not in ROOT.parents,'Output must be external to release')
    return p

def command(argv,cwd,env,timeout=180):
    return subprocess.run(argv,cwd=cwd,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=timeout)

def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize,'Use python3 -I -S -B without optimization')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',required=True);ap.add_argument('--render-dpi',type=int,default=120);ap.add_argument('--require-packaged-match',action='store_true');a=ap.parse_args()
    require(72<=a.render_dpi<=200,'DPI must be 72 through 200')
    before=snapshot();pins=json.loads(file_bytes(ROOT/'manuscript/MANUSCRIPT_PINS.json'))
    require(set(pins)=={'report59.tex','fixture-table.tex','geometry-figure.tex'},'Unexpected manuscript inventory')
    inputs={name:file_bytes(ROOT/'manuscript'/name) for name in pins}
    require(all(sha(inputs[n])==pins[n] for n in pins),'Manuscript pin mismatch')
    require(set(p.name for p in (ROOT/'manuscript').iterdir())==set(pins)|{'MANUSCRIPT_PINS.json'},'Unexpected manuscript file')
    out=destination(a.output_dir)
    binaries={}
    for name in ('pdftex','pdflatex','kpsewhich','pdftotext','pdftoppm','pdfinfo'):
        p=Path('/usr/bin',name).resolve(strict=True);binaries[name]={'path':str(p),'sha256':sha(p.read_bytes())}
    out.mkdir(mode=0o700)
    try:
        with tempfile.TemporaryDirectory(prefix='report59-typeset-') as tmp:
            work=Path(tmp);cache=work/'tex-cache';cache.mkdir();home=work/'home';home.mkdir()
            for name,data in inputs.items():(work/name).write_bytes(data)
            env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC','HOME':str(home),'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1','TEXMF':'{/usr/share/texlive/texmf-dist,/usr/share/texmf}','TEXMFVAR':str(cache),'TEXMFCONFIG':str(cache),'TEXMFHOME':str(home),'TEXFORMATS':str(cache)+':','openin_any':'p','openout_any':'p','shell_escape':'f','MKTEXPK':'0','MKTEXTFM':'0','MKTEXMF':'0'}
            p=command(['/usr/bin/pdftex','-ini','-etex','-no-shell-escape','-recorder','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env)
            (out/'format.log').write_text(p.stdout);require(p.returncode==0,'Fresh format generation failed')
            system={}
            def record_system(p):
                p=p.resolve(strict=True);require(any(str(p).startswith(s) for s in SYSTEM_ROOTS),'Unexpected TeX input: '+str(p));data=p.read_bytes();system[str(p)]={'sha256':sha(data),'bytes':len(data)};return data
            maps=[]
            for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
                p=command(['/usr/bin/kpsewhich',name],work,env,30);require(p.returncode==0 and p.stdout.strip(),'Missing font map '+name);maps.append(record_system(Path(p.stdout.strip())))
            (cache/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n');env['TEXFONTMAPS']=str(cache)+':'
            for n in range(3):
                p=command(['/usr/bin/pdflatex','-no-shell-escape','-recorder','-halt-on-error','-interaction=nonstopmode','-file-line-error','report59.tex'],work,env)
                (out/f'compile-{n+1}.log').write_text(p.stdout);require(p.returncode==0,'LaTeX compilation failed')
            bad=('Overfull \\hbox','Overfull \\vbox','undefined references','undefined citations','Rerun to get cross-references right','Label(s) may have changed','rerunfilecheck Warning')
            require(not any(x in p.stdout for x in bad),'Final layout or reference warning')
            for f,base in ((cache/'pdflatex.fls',cache),(work/'report59.fls',work)):
                for line in f.read_text().splitlines():
                    if line.startswith('INPUT '):
                        p=Path(line[6:]);p=(p if p.is_absolute() else base/p).resolve()
                        if p!=work and work not in p.parents:record_system(p)
            data=file_bytes(work/'report59.pdf');require(data.startswith(b'%PDF-'),'Invalid PDF')
            match=(ROOT/'Report59.pdf').exists() and file_bytes(ROOT/'Report59.pdf')==data
            require(not a.require_packaged_match or match,'Packaged PDF mismatch')
            (out/'Report59.pdf').write_bytes(data);(out/'Report59.log').write_bytes(file_bytes(work/'report59.log'))
            p=command(['/usr/bin/pdftotext','-layout',str(out/'Report59.pdf'),str(out/'Report59.txt')],work,env);require(p.returncode==0,'Text extraction failed')
            p=command(['/usr/bin/pdfinfo',str(out/'Report59.pdf')],work,env);require(p.returncode==0,'PDF info failed');(out/'pdfinfo.txt').write_text(p.stdout)
            pages=out/'pages';pages.mkdir();p=command(['/usr/bin/pdftoppm','-r',str(a.render_dpi),'-png',str(out/'Report59.pdf'),str(pages/'page')],work,env);require(p.returncode==0,'Page rendering failed')
            require(before==snapshot(),'Frozen inputs changed during build')
            (out/'BUILD_DEPENDENCIES.json').write_text(encode({'executables':binaries,'system_inputs':system,'scope':'Installed executable bytes and TeX recorder/font-map inputs; dynamic libraries not inventoried'}))
            files={str(p.relative_to(out)):{'sha256':sha(file_bytes(p)),'bytes':p.stat().st_size} for p in sorted(out.rglob('*')) if p.is_file()}
            receipt={'status':'PASS','source_date_epoch':int(EPOCH),'manuscript_pins':pins,'pdf_sha256':sha(data),'render_dpi':a.render_dpi,'render_pages':len(list(pages.glob('page-*.png'))),'fresh_tex_format':True,'minimal_environment':True,'shell_escape':False,'frozen_inputs_preserved':True,'packaged_pdf_match':match,'files':files,'scope':'Typesetting and analytic figures only; no scientific executable'}
            (out/'BUILD_RECEIPT.json').write_text(encode(receipt));print(encode({k:receipt[k] for k in ('status','pdf_sha256','render_pages')}))
    except BaseException as e:
        (out/'BUILD_FAILURE.json').write_text(encode({'status':'FAIL','error':str(e)}));raise
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,subprocess.SubprocessError) as e:
        print('BUILD REFUSED: '+str(e),file=sys.stderr);raise SystemExit(2)
