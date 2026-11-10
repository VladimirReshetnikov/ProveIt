"""Build the report without network access or shell escape."""
from pathlib import Path
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent

def environment(build):
    """Use installed trees when a minimal image lacks format/font-map caches.

    Adapted from the pinned shared-continuation draft's build.py.
    No packages are downloaded, and an ordinary TeX installation is unchanged.
    """
    env = os.environ.copy()
    def locate(name):
        result = subprocess.run(['kpsewhich', name], env=env,
                                text=True, capture_output=True)
        return result.stdout.strip() if result.returncode == 0 else ''
    if not locate('pdflatex.ini'):
        trees = [p for p in ('/usr/share/texlive/texmf-dist', '/usr/share/texmf')
                 if Path(p).is_dir()]
        if trees:
            env['TEXMF'] = '{' + ','.join(trees) + '}'
    cache = build / 'tex-cache'
    cache.mkdir(exist_ok=True)
    if not locate('pdflatex.fmt'):
        if not locate('pdflatex.ini'):
            raise RuntimeError('The installed TeX distribution lacks pdflatex.ini')
        result = subprocess.run(['pdftex', '-no-shell-escape', '-ini', '-etex',
                                 '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                                cwd=cache, env=env, text=True, capture_output=True)
        (cache/'format_output.txt').write_text(result.stdout+result.stderr)
        if result.returncode:
            raise RuntimeError(result.stdout[-9000:]+result.stderr)
        env['TEXFORMATS'] = str(cache) + os.pathsep + env.get('TEXFORMATS','')
    if not locate('pdftex.map'):
        maps = []
        for name in ('lm.map','cm.map','cmextra.map','symbols.map','euler.map','latxfont.map'):
            path = locate(name)
            if path:
                maps.append(Path(path).read_text())
        if not maps:
            raise RuntimeError('Scalable Latin Modern and AMS font maps are required')
        (cache/'pdftex.map').write_text('\n'.join(maps))
        env['TEXFONTMAPS'] = str(cache) + os.pathsep + env.get('TEXFONTMAPS','')
    return env

def expanded(path):
    text = path.read_text()
    text = re.sub(r'\\input\{([^}]+)\}',
                  lambda match: expanded(ROOT / match.group(1)), text)
    text = re.sub(r'\\lstinputlisting(?:\[([^]]*)\])?\{([^}]+)\}',
                  lambda match: '\\begin{lstlisting}' +
                  ('[' + match.group(1) + ']' if match.group(1) else '') + '\n' +
                  (ROOT / match.group(2)).read_text() + '\\end{lstlisting}', text)
    return text

def main():
    build = ROOT / 'build'
    build.mkdir(exist_ok=True)
    env = environment(build)
    for _ in range(3):
        result = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                                 '-halt-on-error', '-output-directory=build', 'report.tex'],
                                cwd=ROOT, env=env, text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-9000:] + result.stderr)
    shutil.copyfile(build / 'report.pdf', ROOT / 'report.pdf')
    (ROOT / 'ipra_scalar_successor_standalone.tex').write_text(expanded(ROOT / 'report.tex'))
    print(ROOT / 'report.pdf')

if __name__ == '__main__':
    main()
