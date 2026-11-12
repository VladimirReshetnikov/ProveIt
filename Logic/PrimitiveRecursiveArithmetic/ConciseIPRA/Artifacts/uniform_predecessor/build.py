"""Build the complete modular and standalone report with no shell escape."""
from pathlib import Path
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

def environment(work):
    """Bootstrap missing local caches from installed TeX only.

    Adapted from the pinned flat-computation build helper, under the
    upstream license included in reference/PROVEIT_LICENSE.txt.
    """
    env=dict(os.environ)
    probe=subprocess.run(['kpsewhich','pdflatex.fmt'],env=env,capture_output=True,text=True)
    if probe.returncode==0 and probe.stdout.strip():
        return env
    trees=[Path('/usr/share/texmf'),Path('/usr/share/texlive/texmf-dist')]
    if not all(p.is_dir() for p in trees):
        raise RuntimeError('Install a PDFLaTeX distribution before rebuilding')
    cache=work/'texcache';cache.mkdir(exist_ok=True)
    env['TEXMF']='{'+','.join(map(str,[cache,*trees]))+'}'
    target=cache/'web2c/pdftex/pdflatex.fmt';target.parent.mkdir(parents=True,exist_ok=True)
    run=subprocess.run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
                        '-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],
                       cwd=cache,env=env,text=True,capture_output=True)
    if run.returncode:
        raise RuntimeError(run.stdout[-7000:]+run.stderr)
    shutil.move(cache/'pdflatex.fmt',target)
    maps=[trees[0]/'fonts/map/dvips/lm/lm.map']
    maps.extend(sorted((trees[1]/'fonts/map/dvips/amsfonts').glob('*.map')))
    fontmap=cache/'fonts/map/pdftex/local/pdftex.map';fontmap.parent.mkdir(parents=True,exist_ok=True)
    fontmap.write_text('\n'.join(p.read_text() for p in maps))
    return env

def expand(path):
    text=path.read_text()
    def include(match):
        target=ROOT/match.group(1)
        if not target.suffix:
            target=target.with_suffix('.tex')
        return '\n% BEGIN '+str(target.relative_to(ROOT))+'\n'+expand(target)+'\n% END\n'
    text=re.sub(r'\\input\{([^}]+)\}',include,text)
    def listing(match):
        return ('\\begin{lstlisting}'+(match.group(1) or '')+'\n'
                +(ROOT/match.group(2)).read_text().rstrip()+'\n\\end{lstlisting}')
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}',listing,text)

def compile_tex(source,directory,env):
    outputs=[]
    for _ in range(3):
        run=subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                            '-halt-on-error','-output-directory='+str(directory),source.name],
                           cwd=source.parent,env=env,text=True,capture_output=True)
        outputs.append(run.stdout)
        if run.returncode:
            raise RuntimeError(run.stdout[-10000:])
    return outputs

def main():
    standalone=ROOT/'ipra_uniform_predecessor.tex'
    standalone.write_text(expand(ROOT/'report.tex'))
    with tempfile.TemporaryDirectory(prefix='ipra-latex-') as name:
        temporary=Path(name)
        env=environment(temporary)
        logs=compile_tex(ROOT/'report.tex',temporary,env)
        shutil.copyfile(temporary/'report.pdf',ROOT/'report.pdf')
        (ROOT/'evidence/latex_build.log').write_text(logs[-1])
        if '--check-standalone' in sys.argv:
            lone=temporary/'standalone';lone.mkdir()
            shutil.copyfile(standalone,lone/standalone.name)
            compile_tex(lone/standalone.name,lone,env)
            if shutil.which('pdftotext'):
                a=subprocess.check_output(['pdftotext',str(ROOT/'report.pdf'),'-'])
                b=subprocess.check_output(['pdftotext',str(lone/'ipra_uniform_predecessor.pdf'),'-'])
                if a!=b:
                    raise ValueError('Standalone and modular PDF text differ')
    print(ROOT/'report.pdf')

if __name__=='__main__':
    main()
