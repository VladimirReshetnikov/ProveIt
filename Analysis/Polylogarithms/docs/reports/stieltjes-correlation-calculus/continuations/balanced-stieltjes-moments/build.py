"""Compile the standalone article; no network access or repository writes."""
from __future__ import annotations
from pathlib import Path
import datetime, json, os, shutil, subprocess, sys

ROOT=Path(__file__).resolve().parent
ARTICLE=ROOT/'article'
NAME='Balanced_Stieltjes_Moments'

def main():
    exe=shutil.which('pdflatex')
    if exe is None:
        raise SystemExit('pdfLaTeX was not found. Install a TeX distribution with the packages in the preamble.')
    env=os.environ.copy()
    env.setdefault('SOURCE_DATE_EPOCH',str(int(datetime.datetime(2026,10,11,tzinfo=datetime.timezone.utc).timestamp())))
    env.setdefault('FORCE_SOURCE_DATE','1')
    runs=[]
    for run in range(1,4):
        p=subprocess.run([exe,'-interaction=nonstopmode','-halt-on-error',NAME+'.tex'],
                         cwd=ARTICLE,env=env,text=True,encoding='utf-8',errors='replace',
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        runs.append({'pass':run,'returncode':p.returncode})
        if p.returncode:
            print(p.stdout[-12000:])
            raise SystemExit(p.returncode)
    log=(ARTICLE/(NAME+'.log')).read_text(errors='replace')
    unacceptable=[line for line in log.splitlines()
                  if 'Overfull' in line or ('undefined' in line and 'Warning' in line)]
    report={'passes':runs,'pdf_bytes':(ARTICLE/(NAME+'.pdf')).stat().st_size,
            'overfull_or_undefined_warnings':unacceptable,
            'underfull_warnings':sum('Underfull' in line for line in log.splitlines()),
            'source_date_epoch':env['SOURCE_DATE_EPOCH']}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'build_report.json').write_text(json.dumps(report,indent=2)+'\n')
    if unacceptable:
        raise SystemExit('Build finished with unresolved layout/reference warnings; see results/build_report.json')
    print('Built '+str(ARTICLE/(NAME+'.pdf')))

if __name__=='__main__':main()
