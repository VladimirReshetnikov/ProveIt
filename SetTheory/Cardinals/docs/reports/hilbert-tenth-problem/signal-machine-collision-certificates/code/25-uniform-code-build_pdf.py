#!/usr/bin/env python3
"""Build only Report51 locally with installed TeX; no shell escape or network.
The manuscript are copied into a fresh external directory.
"""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
EPOCH='1791072000'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def build(target):
 target=Path(os.path.abspath(target))
 require(all(not p.is_symlink() for p in (target,*target.parents)),'Output symlink rejected')
 target=target.resolve()
 require(target!=ROOT and ROOT not in target.parents,'Output must be outside release')
 require(not target.exists() or (target.is_dir() and not any(target.iterdir())),'Output must be new or empty')
 (target/'manuscript').mkdir(parents=True)
 for rel in ('manuscript/report51.tex',):
  require(not (ROOT/rel).is_symlink(),'Symlink rejected')
  shutil.copyfile(ROOT/rel,target/rel)
 cache=target/'tex-cache';cache.mkdir();cwd=target/'manuscript'
 env=dict(os.environ);env.update(TEXMFVAR=str(cache),TEXMFCONFIG=str(cache),TEXFORMATS=str(cache)+':',TZ='UTC',SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',openout_any='p',openin_any='p')
 def kpse(name):
  p=subprocess.run(['kpsewhich',name],cwd=cwd,env=env,capture_output=True,text=True)
  return p.stdout.strip() if p.returncode==0 else ''
 def run(cmd,where,log):
  with log.open('wb') as f:p=subprocess.run(cmd,cwd=where,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
  require(p.returncode==0,'Build failed: '+str(log))
 if not kpse('article.cls'):env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
 if not kpse('pdflatex.fmt'):
  run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,cache/'format-build.log')
 if not kpse('pdftex.map'):
  data=b''
  for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
   path=kpse(name);require(path,'Missing font map '+name);data+=Path(path).read_bytes()+b'\n'
  (cache/'pdftex.map').write_bytes(data);env['TEXFONTMAPS']=str(cache)+':'
 for n in range(3):run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','report51.tex'],cwd,cwd/f'compile-{n+1}.log')
 pdf=cwd/'report51.pdf';require(pdf.is_file(),'No PDF generated')
 return {'status':'PASS','pdf':str(pdf),'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'pdf_bytes':pdf.stat().st_size,'shell_escape':False,'source_date_epoch':int(EPOCH)}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True,type=Path);a=p.parse_args();print(json.dumps(build(a.output),indent=2,sort_keys=True))
if __name__=='__main__':main()
