#!/usr/bin/env python3
"""Build Report 52 offline in a new directory; never modify the release."""
import sys
if not sys.flags.isolated or sys.flags.optimize:
    raise SystemExit('Use python3 -I without -O')
import argparse, hashlib, json, os, shutil, stat, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
NAME='Research_Report52'
EPOCH='1791072000'
def require(ok,why):
    if not ok: raise RuntimeError(why)
def snapshot():
    data={}
    for p in [ROOT]+sorted(ROOT.rglob('*')):
        s=p.lstat(); require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Unsupported source entry')
        data[p.relative_to(ROOT).as_posix()]=(hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return data
def fresh(path):
    p=path.absolute()
    for a in [p]+list(p.parents): require(not a.is_symlink(),'Output symlink')
    require(not p.exists() and p.parent.is_dir(),'Output must be new with existing parent')
    q=p.resolve(); require(q!=ROOT and ROOT not in q.parents and q not in ROOT.parents,'Output overlaps release')
    return q
def run(cmd,cwd,env,log):
    with log.open('wb') as f:
        r=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=300)
    require(r.returncode==0,'Build failed: '+str(log))
def main():
    a=argparse.ArgumentParser(description=__doc__); a.add_argument('--output',type=Path,required=True);a.add_argument('--check-packaged',action='store_true');a.add_argument('--manifest-sha256');args=a.parse_args()
    out=fresh(args.output); before=snapshot()
    if args.check_packaged:
        require(bool(args.manifest_sha256),'Supply trusted manifest SHA256')
        r=subprocess.run([sys.executable,'-I',str(ROOT/'verify_release.py'),'--manifest-sha256',args.manifest_sha256],capture_output=True,text=True,timeout=120)
        require(r.returncode==0,'Release integrity failed: '+r.stderr)
    out.mkdir();shutil.copyfile(ROOT/(NAME+'.tex'),out/(NAME+'.tex'))
    cache=out/'tex-cache';cache.mkdir()
    env=dict(os.environ);env.update(TEXMFVAR=str(cache),TEXMFCONFIG=str(cache),TEXFORMATS=str(cache)+':',TZ='UTC',SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1')
    def kpse(name):
        p=subprocess.run(['kpsewhich',name],cwd=out,env=env,capture_output=True,text=True,timeout=30)
        return p.stdout.strip() if p.returncode==0 else ''
    if not kpse('article.cls'):env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    if not kpse('pdflatex.fmt'):
        run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env,cache/'format-build.log')
    if not kpse('pdftex.map'):
        raw=b''
        for n in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
            f=kpse(n);require(bool(f),'Missing local font map '+n);raw+=Path(f).read_bytes()+b'\n'
        (cache/'pdftex.map').write_bytes(raw);env['TEXFONTMAPS']=str(cache)+':'
    tex=r'\pdfinfoomitdate=1\pdftrailerid{}\input{'+NAME+'.tex}'
    for n in range(1,4):run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname='+NAME,tex],out,env,out/f'compile-{n}.log')
    result=out/(NAME+'.pdf');require(result.is_file(),'No output PDF')
    require(snapshot()==before,'Release changed during build')
    matches=(ROOT/result.name).is_file() and result.read_bytes()==(ROOT/result.name).read_bytes()
    if args.check_packaged:require(matches,'Packaged PDF differs')
    print(json.dumps({'schema':'report52-pdf-build-v1','status':'PASS','pdf_bytes':result.stat().st_size,'pdf_sha256':hashlib.sha256(result.read_bytes()).hexdigest(),'matches_packaged_pdf':matches,'source_epoch':int(EPOCH),'release_bytes_modes_mtimes_preserved':True,'shell_escape':False,'pdflatex_version':subprocess.run(['pdflatex','--version'],capture_output=True,text=True).stdout.splitlines()[0]},indent=2,sort_keys=True))
if __name__=='__main__':main()
