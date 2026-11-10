"""Build the report from its LaTeX source and record the actual build result."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / 'build'
BUILD.mkdir(exist_ok=True)
# Runtime fallback adapted from the named-specialization draft's build.py.
def environment(work):
    """Use installed TeX sources if the distribution lacks a prebuilt format.

    Fallback adapted from the pinned unparenthesized three-schema archive's
    build.py, which attributes its predecessor in the feedback archive.
    """
    env = dict(os.environ)
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], env=env,
                           capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    trees = [Path('/usr/share/texmf'), Path('/usr/share/texlive/texmf-dist')]
    if not all(path.is_dir() for path in trees):
        raise SystemExit('An installed PDFLaTeX format or TeX source tree is required.')
    cache = work / 'texcache'
    cache.mkdir(exist_ok=True)
    env['TEXMF'] = '{' + ','.join(map(str, [cache, *trees])) + '}'
    target = cache / 'web2c/pdftex/pdflatex.fmt'
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        run = subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
                              '-interaction=nonstopmode', '-halt-on-error',
                              '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                             cwd=cache, env=env, capture_output=True, text=True)
        if run.returncode:
            raise SystemExit(run.stdout[-9000:] + run.stderr)
        shutil.move(cache / 'pdflatex.fmt', target)
    maps = [trees[0] / 'fonts/map/dvips/lm/lm.map']
    maps.extend(sorted((trees[1] / 'fonts/map/dvips/amsfonts').glob('*.map')))
    fontmap = cache / 'fonts/map/pdftex/local/pdftex.map'
    fontmap.parent.mkdir(parents=True, exist_ok=True)
    fontmap.write_text('\n'.join(path.read_text() for path in maps))
    return env

ENV = environment(BUILD)
command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
           '-file-line-error', '-output-directory', str(BUILD), 'report.tex']
def expanded_source(path):
    text = path.read_text()
    def replace_input(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix('.tex')
        return expanded_source(child)
    text = re.sub(r'\\input\{([^}]+)\}', replace_input, text)
    def replace_listing(match):
        options = '[' + match.group(1) + ']' if match.group(1) else ''
        return '\\begin{lstlisting}' + options + '\n' + (ROOT / match.group(2)).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(?:\[([^\]]*)\])?\{([^}]+)\}', replace_listing, text)

(ROOT / 'report_standalone.tex').write_text(expanded_source(ROOT / 'report.tex'))
outputs = []
for number in range(3):
    process = subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True)
    outputs.append(process.stdout + process.stderr)
    if process.returncode:
        (ROOT / 'evidence/latex_build.log').write_text('\n'.join(outputs))
        raise SystemExit('LaTeX failed; see evidence/latex_build.log')
log = (BUILD / 'report.log').read_text()
unresolved = [line for line in log.splitlines()
              if 'undefined' in line.lower() or 'multiply defined' in line.lower()]
if unresolved:
    raise SystemExit('Unresolved LaTeX references: ' + repr(unresolved))
output = ROOT / 'ipra_guarded_elimination.pdf'
shutil.copyfile(BUILD / 'report.pdf', output)
overfull = re.findall(r'Overfull \\[hv]box[^\n]*', log)
result = {'status': 'PASS', 'passes': 3, 'output': output.name,
          'bytes': output.stat().st_size,
          'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
          'overfull_boxes': overfull,
          'visual_review': 'See evidence/pdf_review.json after rendering.'}
(ROOT / 'evidence/latex_build.log').write_text('\n'.join(outputs))
(ROOT / 'evidence/build.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
