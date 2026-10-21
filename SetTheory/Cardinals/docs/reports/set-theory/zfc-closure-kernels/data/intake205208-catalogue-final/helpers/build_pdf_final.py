#!/usr/bin/env python3
"""Own final two-pass catalogue build, validation and changed-page rendering.
This script is prepared but unexecuted until final PASS, root GO and status adoption.
It never writes the maintained PDF; root receives a validated scratch artifact.
"""
import argparse,hashlib,json,os,re,signal,subprocess,time
from pathlib import Path
from update_status import terminal
EXPECTED_MANIFEST='ef043815775ba99b97e337622807d1c97169d0f2b3c81f955255c65b18e0c033'
MANIFEST='SetTheory/Cardinals/docs/reports/manifest.tex'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--status-record',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
 a=ap.parse_args();r=json.loads(a.status_record.read_text());assert r['status']=='APPLIED_FINAL_STATUS_AFTER_PASS'
 actual=r['actual'];assert sha(Path(actual['result']))==actual['result_sha256'] and sha(Path(actual['live_review']))==actual['live_review_sha256']
 values,_=terminal(Path(actual['result']),Path(actual['live_review']))
 assert values==r['values']
 for f in r['files']:assert sha(a.repo/f['path'])==f['after_sha256'],f['path']
 pin=next(f['after_sha256'] for f in r['files'] if f['path']==MANIFEST)
 assert pin==EXPECTED_MANIFEST
 src=(a.repo/MANIFEST).resolve();out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
 (out/'source.tex').write_bytes(src.read_bytes());cwd=(a.repo/'SetTheory/Cardinals/docs/reports').resolve()
 result=dict(status='RUNNING',source=str(src),source_sha256=pin,status_record_sha256=sha(a.status_record),builder_sha256=sha(Path(__file__)),values=values,jobs=[],canonical_pdf_modified=False)
 def persist():save(out/'result.json',result)
 def command(label,argv,cap=120):
  start=time.monotonic();log=out/(label+'.stdout')
  with log.open('wb') as f:
   child=subprocess.Popen(argv,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
   try:code=child.wait(timeout=cap)
   except BaseException:
    if child.poll() is None:os.killpg(child.pid,signal.SIGKILL)
    child.wait();raise
  result['jobs'].append(dict(label=label,argv=argv,exit_code=code,seconds=time.monotonic()-start,stdout_sha256=sha(log)))
  persist();assert code==0,(label,code)
  return log
 persist()
 try:
  command('pdflatex-version',['pdflatex','--version'])
  for n in (1,2):
   command('pass'+str(n),['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-no-shell-escape','-jobname=manifest','-output-directory',str(out),str(src)])
   log=out/'manifest.log';(out/('pass'+str(n)+'.log')).write_bytes(log.read_bytes());assert sha(src)==pin
  log=(out/'manifest.log').read_text(errors='replace')
  diagnostics=[s for s in log.splitlines() if re.search(r'Overfull|Underfull|LaTeX Warning|Package .+ Warning|Missing character|undefined|Rerun to get',s)]
  save(out/'diagnostics.json',diagnostics);assert not diagnostics,diagnostics
  pdf=out/'manifest.pdf';command('pdfinfo',['pdfinfo',str(pdf)]);fonts=command('pdffonts',['pdffonts',str(pdf)])
  fontrows=fonts.read_text().splitlines()[2:];assert fontrows
  # pdffonts trailing columns are emb/sub/uni/object-ID; embedding must be yes.
  assert all(line.split()[-5]=='yes' for line in fontrows if line.strip()),'Unembedded font'
  command('pdftotext',['pdftotext','-layout',str(pdf),str(out/'manifest.txt')])
  pages=(out/'manifest.txt').read_text().split('\f');flat=' '.join(' '.join(pages).split())
  for token in ['290','178','187','1,426','2,240','5314ca0e6b','b07002a86b']:assert token in flat,token
  hits=[i+1 for i,p in enumerate(pages) if ('phase-six' in p or 'phase six' in p or '1,426' in p)]
  assert hits,'No changed status page located'
  rendered=[]
  for page in sorted(set(hits)):
   stem=out/('page-'+str(page));command('render-'+str(page),['pdftoppm','-f',str(page),'-l',str(page),'-r','100','-png','-singlefile',str(pdf),str(stem)])
   image=stem.with_suffix('.png');rendered.append(dict(page=page,path=str(image),sha256=sha(image)))
  assert sha(src)==pin
  result.update(status='PDF_VALIDATED_PENDING_VISUAL_REVIEW',pdf_sha256=sha(pdf),page_count=len([p for p in pages if p.strip()]),diagnostics=0,all_fonts_embedded=True,rendered_pages=rendered,source_unchanged=True)
 except BaseException as e:
  result.update(status='FAILED',exception=repr(e),source_unchanged=sha(src)==pin);raise
 finally:persist()
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
