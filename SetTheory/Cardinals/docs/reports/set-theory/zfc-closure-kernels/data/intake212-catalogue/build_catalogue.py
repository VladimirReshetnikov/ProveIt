#!/usr/bin/env python3
"""Own source-bound two-pass catalogue build; no delivered execution or proof compiler."""
from pathlib import Path
import argparse,hashlib,json,os,re,signal,subprocess,time
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
R=a.repo.resolve();O=a.out.resolve();O.mkdir(parents=True,exist_ok=False)
source=R/'SetTheory/Cardinals/docs/reports/manifest.tex';pin='60b660e340a6970844c7bdd49facd53f884cb77a9bd0dfbe97f3640df970f99c'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
assert sha(source)==pin
(O/'source.tex').write_bytes(source.read_bytes())
r={'status':'RUNNING','source_sha256':pin,'builder_sha256':sha(Path(__file__)),'jobs':[],'proof_compiler_or_delivered_execution':False,'canonical_pdf_changed':False}
def job(name,argv,cap=120):
 t=time.monotonic();log=O/(name+'.stdout')
 with log.open('wb') as f:
  proc=subprocess.Popen(argv,cwd=source.parent,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  try:rc=proc.wait(timeout=cap)
  except BaseException:
   if proc.poll() is None:os.killpg(proc.pid,signal.SIGKILL)
   proc.wait();raise
 r['jobs'].append({'name':name,'argv':argv,'exit_code':rc,'seconds':time.monotonic()-t,'stdout_sha256':sha(log)})
 save(O/'result.json',r);assert rc==0,(name,rc)
 return log
try:
 job('pdflatex-version',['pdflatex','--version'])
 for n in (1,2):
  job('pass'+str(n),['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-no-shell-escape','-jobname=manifest','-output-directory',str(O),str(source)])
  (O/('pass'+str(n)+'.log')).write_bytes((O/'manifest.log').read_bytes());assert sha(source)==pin
 diagnostics=[l for l in (O/'manifest.log').read_text().splitlines() if re.search(r'Overfull|Underfull|LaTeX Warning|Package .+ Warning|Missing character|undefined|Rerun to get',l)]
 save(O/'diagnostics.json',diagnostics);assert not diagnostics,diagnostics
 pdf=O/'manifest.pdf';job('pdfinfo',['pdfinfo',str(pdf)])
 fonts=job('pdffonts',['pdffonts',str(pdf)]).read_text().splitlines()[2:];assert fonts and all(l.split()[-5]=='yes' for l in fonts if l.strip())
 job('pdftotext',['pdftotext','-layout',str(pdf),str(O/'manifest.txt')])
 text=(O/'manifest.txt').read_text();pages=[p for p in text.split('\f') if p.strip()]
 numbers=[int(m[1]) for l in text.splitlines() if (m:=re.match(r'^\s*(\d{1,3})\.\s+(.+)',l))]
 assert numbers==list(range(1,291)),numbers
 flat=' '.join(text.split())
 for expected in ['179','367','1,059','1,426','284,987','9740f2bd13','6f0d42d368','71 only bounded','290']:assert expected in flat,expected
 for i,p in enumerate(pages,1):
  assert p.strip().splitlines()[-1].strip()==str(i),(i,p.strip().splitlines()[-1])
 rendered=[]
 wanted=[i for i,p in enumerate(pages,1) if 'batch 212' in p or 'Batch 212' in p or '284,987' in p or ('179 numbered sources' in p)]
 for i in sorted(set(wanted)):
  job('render-'+str(i),['pdftoppm','-f',str(i),'-l',str(i),'-r','110','-png','-singlefile',str(pdf),str(O/('page-'+str(i)))])
  rendered.append({'page':i,'path':str(O/('page-'+str(i)+'.png')),'sha256':sha(O/('page-'+str(i)+'.png'))})
 assert sha(source)==pin
 r.update(status='PDF_VALIDATED_AWAITING_VISUAL_REVIEW',pdf_sha256=sha(pdf),pdf_bytes=pdf.stat().st_size,pages=len(pages),entries=290,all_page_footers_correct=True,all_fonts_embedded=True,diagnostics=0,rendered=rendered)
except BaseException as e:r.update(status='FAILED',error=repr(e));raise
finally:save(O/'result.json',r)
print(json.dumps(r,indent=2))
