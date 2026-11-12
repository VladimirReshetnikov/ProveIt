"""Make a standalone TeX source and compile the research report."""
from pathlib import Path
import json
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent


def expand(text, stack=()):
    def include(match):
        name=match.group(1)
        if name in stack:
            raise ValueError('Circular TeX input: '+name)
        path=ROOT/name
        if not path.suffix:path=path.with_suffix('.tex')
        return '\n% Begin attributed input: '+name+'\n'+expand(path.read_text(),stack+(name,))+'\n% End input\n'
    text=re.sub(r'\\input\{([^}]+)\}',include,text)
    def listing(match):
        opts=match.group(1) or ''
        path=ROOT/match.group(2)
        return '\\begin{lstlisting}'+opts+'\n'+path.read_text().rstrip()+'\n\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}',listing,text)


standalone=ROOT/'ipra_selfseed_scalar.tex'
standalone.write_text(expand((ROOT/'report.tex').read_text()))
build=ROOT/'tmp/latex';build.mkdir(parents=True,exist_ok=True)
logs=[]
for _ in range(3):
    result=subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode',
                           '-halt-on-error','-output-directory='+str(build),standalone.name],
                          cwd=ROOT,text=True,capture_output=True)
    logs.append(result.stdout+result.stderr)
    if result.returncode:
        (ROOT/'evidence/latex_failure.log').write_text(logs[-1])
        print(logs[-1][-10000:])
        raise SystemExit(result.returncode)
log=(build/'ipra_selfseed_scalar.log').read_text()
warnings=[line for line in log.splitlines() if 'Overfull' in line or 'undefined' in line.lower() or 'multiply defined' in line]
shutil.copy2(build/'ipra_selfseed_scalar.pdf',ROOT/'ipra_selfseed_scalar.pdf')
(ROOT/'evidence/latex_build.json').write_text(json.dumps({'passes':3,'warnings':warnings},indent=2)+'\n')
print(json.dumps({'pdf':str(ROOT/'ipra_selfseed_scalar.pdf'),'warnings':warnings},indent=2))
