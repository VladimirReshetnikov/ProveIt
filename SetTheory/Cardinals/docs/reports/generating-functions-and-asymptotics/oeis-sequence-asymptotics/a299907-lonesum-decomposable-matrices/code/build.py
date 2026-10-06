"""Build in a clean temporary directory; leave all bundle inputs unchanged."""
import sys
sys.dont_write_bytecode=True
import argparse,os,shutil,subprocess,tempfile
from pathlib import Path
from safe_output import preflight,write_new
ROOT=Path(__file__).resolve().parent

def build(destination):
    destination=preflight(destination,ROOT)
    with tempfile.TemporaryDirectory(prefix='report132-build-') as tmp:
        p=Path(tmp);shutil.copy2(ROOT/'Report132.tex',p/'Report132.tex')
        env=os.environ.copy();env.update(SOURCE_DATE_EPOCH='1790899200',FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C',TEXMFVAR=str(p/'texmf-var'),TEXMFCONFIG=str(p/'texmf-config'))
        for d in ['texmf-var','texmf-config']:(p/d).mkdir()
        if Path('/usr/share/texlive/texmf-dist').is_dir():
            env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
        env['TEXFORMATS']=str(p)+'//:'
        fmt=['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini']
        result=subprocess.run(fmt,cwd=p,env=env,capture_output=True,text=True,timeout=120)
        if result.returncode:raise RuntimeError(result.stdout[-10000:]+result.stderr[-2000:])
        source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report132.tex}'
        cmd=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
        for _ in range(2):
            result=subprocess.run(cmd,cwd=p,env=env,capture_output=True,text=True,timeout=180)
            if result.returncode:
                raise RuntimeError(result.stdout[-10000:]+'\n'+result.stderr[-2000:])
        log=(p/'Report132.log').read_text()
        for forbidden in ['Overfull \\hbox','Overfull \\vbox','undefined references','multiply defined','undefined citations','Missing character:','Label(s) may have changed']:
            if forbidden in log:raise RuntimeError('TeX QA warning: '+forbidden)
        write_new(destination,(p/'Report132.pdf').read_bytes(),ROOT)
    return destination

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',required=True,help='PDF output path; use an external directory to preserve bundle integrity')
    args=p.parse_args();print(build(args.output))
if __name__=='__main__':main()
