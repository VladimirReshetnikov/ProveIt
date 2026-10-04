#!/usr/bin/env python3
"""Verify a Report49 manifest and replay inspected local sources in scratch.
Only Python's standard library is needed except installed g++/TeX commands.
No networking, source mutation, downloaded executable, or schedule is used.
"""
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
 out={}
 for p in [ROOT,*sorted(ROOT.rglob('*'))]:
  st=p.lstat();require(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode),'Symlink or special file rejected: '+str(p))
  out[p.relative_to(ROOT).as_posix()]=(sha(p) if p.is_file() else None,stat.S_IMODE(st.st_mode),st.st_mtime_ns)
 return out

def verify(trusted):
 mf=ROOT/'MANIFEST.sha256';require(mf.is_file(),'Manifest missing')
 require(len(trusted)==64 and all(c in '0123456789abcdef' for c in trusted),'Pass the trusted lowercase manifest SHA-256')
 require(sha(mf)==trusted,'Manifest digest does not match trusted identity')
 names=[]
 for line in mf.read_text().splitlines():
  digest,rel=line.split('  ',1);p=Path(rel)
  require(not p.is_absolute() and '..' not in p.parts and rel==p.as_posix() and rel!='MANIFEST.sha256','Unsafe manifest path')
  require(rel not in names,'Duplicate manifest entry');names.append(rel)
  require((ROOT/p).is_file() and not (ROOT/p).is_symlink(),'Missing or unsafe member '+rel)
  require(sha(ROOT/p)==digest,'Checksum mismatch '+rel)
 actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()}
 require(actual==set(names)|{'MANIFEST.sha256'},'Unlisted or missing release file')
 # Original audit manifest remains a separately authenticated scientific packet.
 af=ROOT/'frozen/audit/SHA256SUMS'
 require(sha(af)=='47e602d8d935baad3eba4dd7ec54c2902a56e4e3eda4d847b9b2c88ccaab7ff7','Original audit manifest changed')
 for line in af.read_text().splitlines():
  h,name=line.split(None,1);name=name.strip().lstrip('*')
  require('/' not in name and name not in ('.','..'),'Unsafe audit member')
  require(sha(af.parent/name)==h,'Frozen audit mismatch '+name)
 prov=json.loads((af.parent/'source-provenance.json').read_text());article=(af.parent/'inherited-article-source.tex').read_bytes()
 require(hashlib.sha256(article).hexdigest()==prov['sha256'],'Inherited article hash')
 require(hashlib.sha1(b'blob '+str(len(article)).encode()+b'\0'+article).hexdigest()==prov['git_blob_sha1'],'Inherited Git blob identity')
 lo,hi=prov['excerpt_lines_inclusive'];excerpt=b''.join(article.splitlines(keepends=True)[lo-1:hi])
 require(excerpt==(af.parent/prov['excerpt_file']).read_bytes(),'Inherited exact line excerpt')
 review=json.loads((ROOT/'frozen/manuscript-audit/verdict.json').read_text())
 require(sha(ROOT/'manuscript/report49.tex')==review['tex_sha256'],'Manuscript review binding changed')
 require(sha(ROOT/'report49.pdf')==review['pdf_sha256'],'PDF review binding changed')
 return len(names)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--verify-only',action='store_true');ap.add_argument('--sanitizer',action='store_true');ap.add_argument('--skip-pdf',action='store_true');ap.add_argument('--output',type=Path,help='new/empty external directory; otherwise create /tmp scratch')
 a=ap.parse_args();before=snapshot();count=verify(a.manifest_sha256)
 report={'status':'PASS','verified_files':count,'manifest_sha256':a.manifest_sha256,'network_used':False,'upstream_code_executed':False}
 if not a.verify_only:
  work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='report49-replay-'))
  require(work!=ROOT and ROOT not in work.parents,'Scratch must be outside release')
  require(not work.exists() or (work.is_dir() and not any(work.iterdir())),'Scratch must be new or empty')
  work.mkdir(parents=True,exist_ok=True);(work/'candidate').mkdir();(work/'audit').mkdir();(work/'manuscript-audit').mkdir();env=dict(os.environ);env.update(PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1',TZ='UTC');env.pop('PYTHONPATH',None)
  allowed={'candidate':['check_reversible_clock.py'],'audit':['independent_checker.py','check_corollaries.py','exhaustive_periodic.cpp'],'manuscript-audit':['manuscript_checker.py']}
  for kind,names in allowed.items():
   for name in names:shutil.copyfile(ROOT/'frozen'/kind/name,work/kind/name)
  def run(command,cwd,log,timeout=1200):
   with (work/log).open('wb') as f:p=subprocess.run(command,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=timeout)
   require(p.returncode==0,'Replay command failed; inspect '+str(work/log))
  run([sys.executable,'-I','-B','check_reversible_clock.py','--output','checker-results.json'],work/'candidate','candidate.log')
  require(json.loads((work/'candidate/checker-results.json').read_text())==json.loads((ROOT/'frozen/candidate/checker-results.json').read_text()),'Candidate receipt changed')
  run([sys.executable,'-I','-B','independent_checker.py'],work/'audit','independent.log')
  def without_elapsed(p):
   obj=json.loads(p.read_text());obj.pop('elapsed_seconds',None);return obj
  require(without_elapsed(work/'audit/independent-results.json')==without_elapsed(ROOT/'frozen/audit/independent-results.json'),'Sparse audit receipt changed')
  require((work/'audit/critical-overlap-truth-tables.json').read_bytes()==(ROOT/'frozen/audit/critical-overlap-truth-tables.json').read_bytes(),'Overlap tables differ')
  bootstrap="import runpy,sys;sys.path.insert(0,sys.argv[1]);runpy.run_path(sys.argv[2],run_name='__main__')"
  run([sys.executable,'-I','-B','-c',bootstrap,str(work/'audit'),str(work/'audit/check_corollaries.py')],work/'audit','corollaries.log')
  require((work/'audit/corollary-results.json').read_bytes()==(ROOT/'frozen/audit/corollary-results.json').read_bytes(),'Corollary receipt changed')
  run([sys.executable,'-I','-B','manuscript_checker.py'],work/'manuscript-audit','manuscript-check-results.json')
  require((work/'manuscript-check-results.json').read_bytes()==(ROOT/'frozen/manuscript-audit/manuscript-check-results.json').read_bytes(),'Manuscript checker receipt differs')
  compiler=shutil.which('g++');require(compiler,'g++ not found')
  run([compiler,'-std=c++17','-O2','-Wall','-Wextra','-pedantic','exhaustive_periodic.cpp','-o','periodic'],work/'audit','compile.log')
  run([str(work/'audit/periodic')],work/'audit','periodic-results.json')
  require((work/'periodic-results.json').read_bytes()==(ROOT/'frozen/audit/periodic-results.json').read_bytes(),'Periodic receipt differs')
  if a.sanitizer:
   run([compiler,'-std=c++17','-O1','-g','-fsanitize=undefined','-fno-sanitize-recover=all','-Wall','-Wextra','-pedantic','exhaustive_periodic.cpp','-o','periodic-ubsan'],work/'audit','compile-ubsan.log')
   run([str(work/'audit/periodic-ubsan')],work/'audit','periodic-ubsan-results.json')
   require((work/'periodic-ubsan-results.json').read_bytes()==(ROOT/'frozen/audit/periodic-ubsan-results.json').read_bytes(),'UBSan receipt differs')
  run([sys.executable,'-I','-B',str(ROOT/'code/make_figure.py'),'--trace-only','--output-dir',str(work/'figure')],work,'figure.log')
  for name in ['clock-spacetime.csv','figure-receipt.json']:
   require((work/'figure'/name).read_bytes()==(ROOT/'figures'/name).read_bytes(),'Figure data differs '+name)
  if not a.skip_pdf:
   run([sys.executable,'-I','-B',str(ROOT/'code/build_pdf.py'),'--output',str(work/'pdf')],work,'pdf-build.json')
   require((work/'pdf/manuscript/report49.pdf').read_bytes()==(ROOT/'report49.pdf').read_bytes(),'PDF bytes differ; use the recorded TeX engine and fonts')
  report.update({'scratch':str(work),'candidate_receipt':'exact JSON equality','independent_receipt':'exact equality except elapsed_seconds','overlap_tables':'byte identical','corollary_receipt':'byte identical','manuscript_receipt':'byte identical','periodic_receipt':'byte identical','sanitizer_replayed':a.sanitizer,'figure_trace':'byte identical','pdf_rebuilt':not a.skip_pdf,'pdf_byte_identical':not a.skip_pdf})
 require(snapshot()==before,'Release bytes, modes, or mtimes changed')
 report['original_bytes_modes_mtimes_preserved']=True
 if not a.verify_only:(work/'replay-result.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
 print(json.dumps(report,indent=2,sort_keys=True))
if __name__=='__main__':main()
