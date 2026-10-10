#!/usr/bin/env python3
"""Build the standalone article and reject unresolved references/overfull boxes."""
from __future__ import annotations
import datetime,json,platform,re,shutil,subprocess,tempfile,time
from pathlib import Path

def main():
    root=Path(__file__).resolve().parents[1]
    engine=shutil.which('pdflatex')
    if not engine:raise SystemExit('pdfLaTeX was not found. Install TeX Live and put pdflatex on PATH.')
    start=time.time()
    version=subprocess.check_output([engine,'--version'],text=True).splitlines()[0]
    with tempfile.TemporaryDirectory(prefix='nested-harmonic-jets-') as tmp:
        cmd=[engine,'-interaction=nonstopmode','-halt-on-error',f'-output-directory={tmp}','article.tex']
        for i in range(3):
            run=subprocess.run(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,errors='replace')
            if run.returncode:
                print(run.stdout)
                raise SystemExit(f'LaTeX pass {i+1} failed.')
        log=(Path(tmp)/'article.log').read_text(errors='replace')
        errors=[x for x in ['Overfull','There were undefined references','undefined citations','Rerun to get cross-references right'] if x in log]
        if re.search(r'LaTeX Warning: (Reference|Citation).*undefined',log):errors.append('unresolved reference/citation')
        if errors:raise SystemExit('PDF QA failed: '+', '.join(errors))
        shutil.copy2(Path(tmp)/'article.pdf',root/'article.pdf')
        pages=re.search(r'Output written on .*?\((\d+) pages',log,re.S)
        report={'status':'PASS','passes':3,'engine':version,'python':platform.python_version(),
                'built_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.time()-start,
                'pages':int(pages.group(1)) if pages else None,'pdf_bytes':(root/'article.pdf').stat().st_size,
                'overfull_boxes':log.count('Overfull'),'underfull_boxes':log.count('Underfull'),
                'unresolved_references_or_citations':False,
                'note':'Build checks do not replace mathematical review or rendered-page inspection.'}
        (root/'results'/'build_report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2))
if __name__=='__main__':main()
