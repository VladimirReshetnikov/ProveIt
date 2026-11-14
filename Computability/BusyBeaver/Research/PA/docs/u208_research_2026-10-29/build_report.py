#!/usr/bin/env python3
"""Build only this newly authored report with shell escape disabled."""
import argparse,os,subprocess,tempfile
from pathlib import Path


def tex_environment(cache):
    env=os.environ.copy()
    # Explicit search paths also support a read-only Debian TeX installation
    # whose generated ls-R/format configuration is absent. No system writes.
    roots=[p for p in (Path('/usr/share/texlive/texmf-dist'),Path('/usr/share/texmf')) if p.is_dir()]
    if roots:
        env['TEXINPUTS']='.:'+':'.join(str(p/'tex')+'//' for p in roots)+':'
        for key,sub in [('TEXFONTMAPS','map'),('TFMFONTS','tfm'),('T1FONTS','type1'),('VFFONTS','vf'),('ENCFONTS','enc')]:
            env[key]=':'.join(str(p/'fonts'/sub)+'//' for p in roots)+':'
        cache.mkdir(parents=True,exist_ok=True)
        maps=[Path('/usr/share/texmf/fonts/map/dvips/lm/lm.map')]+[Path('/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts')/name for name in ('cm.map','cmextra.map','symbols.map','latxfont.map')]
        (cache/'pdftex.map').write_bytes(b'\n'.join(p.read_bytes() for p in maps if p.exists()))
        env['TEXFONTMAPS']=str(cache)+'//:'+env['TEXFONTMAPS']
        env['TEXFORMATS']=str(cache)+'//:'
        env['TEXMFVAR']=str(cache/'var');env['TEXMFCONFIG']=str(cache/'config')
        ini=Path('/usr/share/texlive/texmf-dist/tex/latex/tex-ini-files/pdflatex.ini')
        if ini.exists():
            run(['pdftex','-ini','-etex','-no-shell-escape','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env,cache/'format.log')
    return env


def run(command,cwd,env,log):
    proc=subprocess.run(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_bytes(proc.stdout)
    if proc.returncode:raise RuntimeError(proc.stdout.decode(errors='replace')[-16000:])


def build(source):
    source=source.resolve()
    with tempfile.TemporaryDirectory(prefix='u208-tex-') as tmp:
        env=tex_environment(Path(tmp))
        for n in (1,2):run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','report.tex'],source,env,source/('build'+str(n)+'.log'))
    return source/'report.pdf'


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=Path('report'));a=p.parse_args();print(build(a.source))
