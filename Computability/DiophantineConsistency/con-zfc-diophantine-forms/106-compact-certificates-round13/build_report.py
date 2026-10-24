#!/usr/bin/env python3
"""Build the editable report with the caller's installed pdfLaTeX."""
import argparse,os,pathlib,shutil,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parent
NAME='ConZFC_Compact_Proof_Certificates_Round13_2026-10-24'
p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
if a.output.resolve().is_relative_to(ROOT):raise ValueError('Output must be outside the release directory.')
a.output.mkdir(parents=True,exist_ok=True)
with tempfile.TemporaryDirectory(prefix='round13-report-')as t:
 d=pathlib.Path(t);shutil.copyfile(ROOT/(NAME+'.tex'),d/(NAME+'.tex'))
 env=dict(os.environ,SOURCE_DATE_EPOCH='1792800000',TZ='UTC')
 for _ in range(2):subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-no-shell-escape',NAME+'.tex'],cwd=d,env=env,check=True)
 shutil.copyfile(d/(NAME+'.pdf'),a.output/(NAME+'.pdf'))
print(a.output/(NAME+'.pdf'))
