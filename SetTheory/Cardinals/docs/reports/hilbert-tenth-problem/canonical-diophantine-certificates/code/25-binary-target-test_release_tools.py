#!/usr/bin/env python3
"""Fresh local tests of Report 52 integrity/archive/path handling on copies."""
import sys
if not sys.flags.isolated or sys.flags.optimize:raise SystemExit('Use python3 -I without -O')
import argparse,hashlib,json,os,shutil,stat,subprocess,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def require(ok,why):
    if not ok:raise RuntimeError(why)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(root):
    out={}
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat();require(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode),'Unsafe source entry')
        out[p.relative_to(root).as_posix()]=(sha(p) if p.is_file() else None,s.st_mode,s.st_mtime_ns)
    return out
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();out=a.output.absolute()
    require('..' not in a.output.parts,'Parent traversal forbidden')
    for p in [out]+list(out.parents):require(not p.is_symlink(),'Symlink output')
    require(not out.exists() and out.parent.is_dir(),'Output must be new with existing parent');out=out.resolve();require(out!=ROOT and ROOT not in out.parents and out not in ROOT.parents,'Overlapping output')
    before=snap(ROOT);out.mkdir();r=out/'copied-release';shutil.copytree(ROOT,r,copy_function=shutil.copy2)
    pins={}
    for p in sorted(r.rglob('*')):
        if p.is_file() and p != r/'MANIFEST.json':
            pins[p.relative_to(r).as_posix()]={'bytes':p.stat().st_size,'mode':stat.S_IMODE(p.stat().st_mode),'sha256':sha(p)}
    (r/'MANIFEST.json').write_text(json.dumps({'schema':'report52-inventory-v1','files':pins},sort_keys=True,indent=2)+'\n');trusted=sha(r/'MANIFEST.json')
    results=[]
    def call(name,args,ok=True,flags=('-I',)):
        p=subprocess.run([sys.executable,*flags,str(r/name),*map(str,args)],capture_output=True,text=True,timeout=120)
        require((p.returncode==0)==ok,'Unexpected status '+name+' '+str(args)+': '+p.stdout+p.stderr)
        results.append({'tool':name,'expected_success':ok,'passed':True});return p
    args=['--manifest-sha256',trusted]
    call('verify_release.py',args)
    call('verify_release.py',['--manifest-sha256','0'*64],False)
    (r/'extra.txt').write_text('extra');call('verify_release.py',args,False);(r/'extra.txt').unlink()
    f=r/'Research_Report52.pdf';saved=f.read_bytes();f.write_bytes(saved+b'corruption');call('verify_release.py',args,False);f.write_bytes(saved)
    f=r/'Research_Report52.tex';saved=f.read_bytes();f.unlink();call('verify_release.py',args,False);f.write_bytes(saved)
    os.symlink('Research_Report52.tex',r/'bad-link');call('verify_release.py',args,False);(r/'bad-link').unlink()
    os.mkfifo(r/'bad-fifo');call('verify_release.py',args,False);(r/'bad-fifo').unlink()
    call('verify_release.py',args,False,flags=())
    call('verify_release.py',args,False,flags=('-I','-O'))
    moved=out/'relocated-release';r.rename(moved);r=moved;call('verify_release.py',args)
    for n in ('a.zip','b.zip'):call('archive_release.py',['--output',out/n,*args])
    require((out/'a.zip').read_bytes()==(out/'b.zip').read_bytes(),'Archives differ');results.append({'test':'archive_byte_identity','passed':True})
    with zipfile.ZipFile(out/'a.zip') as z:
        require(all(i.compress_type==zipfile.ZIP_STORED and i.date_time==(2026,10,4,0,0,0) and i.external_attr>>16==stat.S_IFREG|0o644 for i in z.infolist()),'ZIP attributes')
        require(z.namelist()==sorted(z.namelist()),'ZIP order');results.append({'test':'archive_fixed_attributes','passed':True})
    call('archive_release.py',['--output',out/'a.zip',*args],False)
    call('archive_release.py',['--output',r/'bad.zip',*args],False)
    call('archive_release.py',['--output',out/'absent'/'bad.zip',*args],False)
    call('archive_release.py',['--output',out/'bad.zip',*args],False,flags=('-I','-O'))
    call('build_pdf.py',['--output',r/'new-build'],False)
    call('build_pdf.py',['--output',r],False)
    call('build_pdf.py',['--output',out/'absent'/'new-build'],False)
    call('build_pdf.py',['--output',out/'new-build'],False,flags=())
    require(snap(ROOT)==before,'Original release was changed')
    result={'schema':'report52-release-tool-tests-v1','status':'PASS','test_count':len(results),'tests':results,'relocated_verification_passed':True,'archive_bytes_identical':True,'original_bytes_modes_mtimes_preserved':True,'actual_pdf_rebuild_test':'separate verification/pdf-build.json'}
    (out/'test-results.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':main()
