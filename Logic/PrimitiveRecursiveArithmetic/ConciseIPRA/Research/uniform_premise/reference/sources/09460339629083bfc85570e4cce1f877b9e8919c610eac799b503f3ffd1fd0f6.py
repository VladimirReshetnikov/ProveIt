"""Compile both complete LaTeX sources without network access or shell escape."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def flatten():
    text = (ROOT / 'report.tex').read_text()
    code = (ROOT / 'code/checker.py').read_text().rstrip()
    text = text.replace('\\lstinputlisting{code/checker.py}',
                        '\\begin{lstlisting}\n'+code+'\n\\end{lstlisting}')
    token = ('\\IfFileExists{evidence/validation_summary.tex}{\\input{evidence/validation_summary.tex}}{\n'
             'The generated validation receipt is supplied in the evidence directory.}')
    summary = (ROOT / 'evidence/validation_summary.tex').read_text()
    if token not in text:
        raise ValueError('Validation summary placeholder not found')
    text = text.replace(token, summary)
    path = ROOT / 'ipra_atomic_transport_standalone.tex'
    path.write_text(text)
    return path


def compile_tex(path, work, env):
    for _ in range(3):
        result = subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                                 '-halt-on-error',str(path)],cwd=work,text=True,
                                stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=90,env=env)
        if result.returncode:
            raise RuntimeError(result.stdout[-12000:])


if __name__ == '__main__':
    standalone = flatten()
    env = os.environ.copy()
    def locate(name):
        r = subprocess.run(['kpsewhich',name],env=env,text=True,capture_output=True)
        return r.stdout.strip() if r.returncode == 0 else ''
    # Minimal installed TeX trees can lack their generated search databases.
    # Use recursive installed-tree search, not a network package installation.
    if not locate('pdflatex.ini'):
        roots = [p for p in ['/usr/share/texlive/texmf-dist','/usr/share/texmf','/etc/texmf']
                 if Path(p).is_dir()]
        if roots:
            env['TEXMF'] = '{'+','.join(roots)+'}'
            env['TEXMFDBS'] = env['TEXMF']
    with tempfile.TemporaryDirectory(prefix='ipra-tex-') as temp:
        temp = Path(temp)
        if not locate('pdflatex.fmt'):
            r = subprocess.run(['pdftex','-ini','-etex','-jobname=pdflatex',
                                '-progname=pdflatex','pdflatex.ini'],cwd=temp,env=env,
                               text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=90)
            if r.returncode:
                raise RuntimeError(r.stdout[-12000:])
            env['TEXFORMATS'] = str(temp)+os.pathsep+env.get('TEXFORMATS','')
        if not locate('pdftex.map'):
            maps = [locate(n) for n in ['lm.map','cm.map','cmextra.map','symbols.map',
                                        'euler.map','latxfont.map']]
            (temp/'pdftex.map').write_text('\n'.join(Path(p).read_text() for p in maps if p))
            env['TEXFONTMAPS'] = str(temp)+os.pathsep+env.get('TEXFONTMAPS','')
        compile_tex(ROOT / 'report.tex', ROOT, env)
        isolated = temp/'isolated'
        isolated.mkdir()
        local = isolated / standalone.name
        shutil.copy2(standalone,local)
        compile_tex(local,isolated,env)
    shutil.copy2(ROOT/'report.log',ROOT/'evidence/latex_build.log')
    print('Compiled report.pdf; standalone source also compiled in isolation.')
