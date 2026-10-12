"""Build the modular and single-file article, with deterministic source assembly."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, sys, time
ROOT=Path(__file__).resolve().parent
NAME='Universal_Gamma_Normal_Forms'

def assemble(path):
    text=path.read_text(encoding='utf-8')
    def include(match):
        child=ROOT/(match.group(1)+'.tex')
        return '\n% BEGIN '+str(child.relative_to(ROOT))+'\n'+assemble(child)+'\n% END '+str(child.relative_to(ROOT))+'\n'
    return re.sub(r'\\input\{([^}]+)\}',include,text)

def main():
    if not shutil.which('pdflatex'):
        raise SystemExit('pdfLaTeX was not found. Install a TeX distribution, then rerun build.py.')
    source=ROOT/(NAME+'.tex'); source.write_text(assemble(ROOT/'article.tex'),encoding='utf-8')
    start=time.perf_counter()
    for _ in range(3):
        result=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',NAME+'.tex'],
                              cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if result.returncode:
            print(result.stdout[-12000:]);raise SystemExit(result.returncode)
    log=(ROOT/(NAME+'.log')).read_text(errors='replace')
    issues=[line for line in log.splitlines() if 'Overfull' in line or 'undefined' in line.lower() or 'multiply defined' in line.lower()]
    pages=re.search(r'Output written on .*?\((\d+) pages?',log,re.S)
    report={'result':'PASS' if not issues else 'REVIEW','engine':'pdfLaTeX','passes':3,
            'pages':int(pages.group(1)) if pages else None,'issues':issues,
            'elapsed_seconds':time.perf_counter()-start,
            'pdf_sha256':hashlib.sha256((ROOT/(NAME+'.pdf')).read_bytes()).hexdigest()}
    (ROOT/'data'/'pdf_build.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
