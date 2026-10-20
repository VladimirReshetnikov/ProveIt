#!/usr/bin/env python3
"""Build the supplied LaTeX report and regenerate its exact transition table.

Requires Python 3.10+ and pdflatex with the packages named in main.tex.
All temporary files are written to the specified output directory.
"""
from pathlib import Path
import argparse, datetime, hashlib, os, shutil, subprocess

ROOT=Path(__file__).resolve().parents[1]
EXPECTED='60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1'

def table_tex():
    raw=(ROOT/'machine/candidate222.tm').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=EXPECTED:
        raise ValueError('Unexpected canonical machine')
    table={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();table[int(q),int(b)]=(w,d,z)
    if set(table)!={(q,b) for q in range(222) for b in (0,1)}:
        raise ValueError('Wrong state/read inventory')
    rows=[r'\begingroup\small',
          r'\renewcommand{\arraystretch}{0.9}',
          r'\setlength{\tabcolsep}{9pt}',
          r'\begin{longtable}{@{}rcc@{\hspace{14mm}}rcc@{}}',
          r'\toprule',
          r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
          r'\midrule\endfirsthead',
          r'\toprule',
          r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
          r'\midrule\endhead',
          r'\midrule\multicolumn{6}{r}{\small Continued on the next page}\\\endfoot',
          r'\bottomrule\endlastfoot']
    for q in range(111):
        fields=[]
        for state in (q,q+111):
            fields.append(str(state))
            for b in (0,1):
                w,d,z=table[state,b]
                fields.append(r'\texttt{'+f'{w} {d} {z}'+r'}')
        rows.append(' & '.join(fields)+r'\\')
    rows.extend([r'\end{longtable}',r'\endgroup'])
    return '\n'.join(rows)+'\n'

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--table-only',action='store_true')
    a=p.parse_args();out=a.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    (out/'transition_table.tex').write_text(table_tex())
    if a.table_only:return
    for name in ('main.tex','logic.tex'):
        source=ROOT/'report'/name
        if source.resolve()!=out/name:shutil.copy2(source,out/name)
    epoch=int(datetime.datetime(2026,10,20,tzinfo=datetime.timezone.utc).timestamp())
    env={**os.environ,'SOURCE_DATE_EPOCH':str(epoch),'FORCE_SOURCE_DATE':'1'}
    for i in (1,2):
        with (out/f'pdflatex-pass{i}.txt').open('w') as stream:
            subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                            '-file-line-error','main.tex'],cwd=out,env=env,
                            stdout=stream,stderr=subprocess.STDOUT,check=True)
    target=out/'ZFC_K222_Construction_2026-10-20.pdf'
    shutil.copy2(out/'main.pdf',target)
    print(target)

if __name__=='__main__':main()
