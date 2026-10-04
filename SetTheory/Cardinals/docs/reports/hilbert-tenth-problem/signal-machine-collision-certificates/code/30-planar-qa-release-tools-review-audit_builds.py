#!/usr/bin/env python3
"""Run authenticated isolated Report60 builds under clean and poisoned environments."""
import argparse,hashlib,json,os,shutil,stat,subprocess
from pathlib import Path

def enc(v):return (json.dumps(v,sort_keys=True,indent=2)+'\n').encode()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def snap(r):
 d={}
 for p in sorted(r.rglob('*')):
  s=p.lstat()
  require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'nonregular source')
  if stat.S_ISREG(s.st_mode):d[p.relative_to(r).as_posix()]={'sha256':sha(p),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
 return d

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',required=True);ap.add_argument('--output',required=True);a=ap.parse_args();r=Path(a.source);o=Path(a.output);o.mkdir();baseline=snap(r);(o/'source-before.json').write_bytes(enc(baseline));poison=o/'poison-inputs';poison.mkdir();marker=o/'CONTAMINATION_EXECUTED'
 (poison/'sitecustomize.py').write_text('from pathlib import Path\nPath('+repr(str(marker))+').write_text("sitecustomize")\n')
 for exe in ('pdftex','pdflatex','kpsewhich','pdftoppm','pdftotext','pdfinfo'):
  p=poison/exe;p.write_text('#!/bin/sh\nprintf contaminated > '+str(marker)+'\nexit 99\n');p.chmod(0o755)
 (poison/'article.cls').write_text('\\errmessage{HOSTILE CLASS LOADED}\n')
 (poison/'pdflatex.fmt').write_text('HOSTILE FORMAT\n')
 (poison/'texmf.cnf').write_text('shell_escape=t\nopenin_any=a\nopenout_any=a\n')
 clean={'PATH':'/usr/bin:/bin','HOME':str(o),'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC'}
 bad=dict(os.environ);bad.update(PATH=str(poison),HOME=str(poison),TEXINPUTS=str(poison)+'//:',TEXFORMATS=str(poison),TEXMFCNF=str(poison),TEXMF=str(poison),TEXMFHOME=str(poison),TEXMFVAR=str(poison),TEXMFCONFIG=str(poison),TEXFONTMAPS=str(poison),PYTHONPATH=str(poison),PYTHONHOME='/nonexistent-python-home',PYTHONOPTIMIZE='2',PYTHONSTARTUP=str(poison/'sitecustomize.py'),SOURCE_DATE_EPOCH='1',FORCE_SOURCE_DATE='0',TZ='Pacific/Honolulu',openin_any='a',openout_any='a',shell_escape='t')
 results=[]
 for label,env in [('clean',clean),('hostile',bad)]:
  out=o/label;argv=['/usr/bin/python3','-I','-S','-B',str(r/'tools/build_report60.py'),'--output-dir',str(out),'--require-packaged-match']
  p=subprocess.run(argv,cwd=poison,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=360)
  result={'label':label,'argv':argv,'returncode':p.returncode,'stdout':p.stdout.decode(errors='replace'),'stderr':p.stderr.decode(errors='replace')};results.append(result);(o/'RUNS.json').write_bytes(enc(results));require(p.returncode==0,label+' build failed: '+result['stderr'])
  receipt=json.loads((out/'BUILD_RECEIPT.json').read_bytes());pages=sorted((out/'pages').glob('page-*.png'));info=(out/'pdfinfo.txt').read_text();declared=int(next(x.split(':')[1].strip() for x in info.splitlines() if x.startswith('Pages:')))
  require(len(pages)==declared==receipt['render_pages']>0,'Rendered page count mismatch')
  require(all(x.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for x in pages),'PNG signature mismatch')
  require(sha(out/'Report60.pdf')==receipt['pdf_sha256']==sha(r/'Report60.pdf'),'Evidence PDF bytes mismatch')
  require(baseline==snap(r),'Build mutated source files')
  require(not marker.exists(),'Hostile code ran')
  (out/'PAGE_HASHES.json').write_bytes(enc({x.name:sha(x) for x in pages}))
 cleanroot=o/'clean';hostileroot=o/'hostile'
 for name in ('Report60.pdf','Report60.txt','BUILD_DEPENDENCIES.json','BUILD_RECEIPT.json','PAGE_HASHES.json'):
  require((cleanroot/name).read_bytes()==(hostileroot/name).read_bytes(),'Clean/hostile mismatch: '+name)
 summary={'clean_hostile_pdf_text_receipt_dependencies_and_pages_equal':True,'builds':results,'source_preserved':baseline==snap(r),'tool_sha256':sha(r/'tools/build_report60.py'),'contamination_marker_absent':not marker.exists()}
 (o/'source-after.json').write_bytes(enc(snap(r)));(o/'SUMMARY.json').write_bytes(enc(summary));print(enc(summary).decode())
if __name__=='__main__':main()
