#!/usr/bin/env python3
"""Fresh isolated tests of Report 53 release tools against external copies.
Never executes scientific builders, author checkers, upstream programs, or Lean.
"""
import sys
if not sys.flags.isolated or sys.flags.optimize: raise SystemExit('Use python3 -I without -O')
import argparse,hashlib,json,os,shutil,stat,subprocess,zipfile
from pathlib import Path

def require(ok,message):
    if not ok:raise RuntimeError(message)

def digest(b):return hashlib.sha256(b).hexdigest()

def snapshot(root):
    output={}
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat();rel='.' if p==root else str(p.relative_to(root))
        require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Nonregular source entry')
        output[rel]=(stat.S_IMODE(s.st_mode),s.st_mtime_ns,digest(p.read_bytes()) if p.is_file() else None)
    return output

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    root=Path(__file__).resolve().parent.parent;out=args.output.absolute()
    for p in [out]+list(out.parents):require(not p.is_symlink(),'Symlink output')
    require(not out.exists() and out.parent.is_dir(),'Need fresh output with existing parent')
    out=out.resolve();require(root not in out.parents and out not in root.parents and root!=out,'Output overlaps source')
    before=snapshot(root);out.mkdir();fixture=out/'staged release';shutil.copytree(root,fixture)
    # A copied prior seal is omitted before making a fresh fixture seal; never touch live source.
    if (fixture/'MANIFEST.json').exists():(fixture/'MANIFEST.json').unlink()
    def command(where,*args,ok=True,label='command'):
        r=subprocess.run([sys.executable,'-I',str(where/'release.py'),*map(str,args)],capture_output=True,text=True,timeout=300)
        (out/(label+'.stdout')).write_text(r.stdout);(out/(label+'.stderr')).write_text(r.stderr)
        require((r.returncode==0)==ok,'Unexpected command result: '+label)
        return json.loads(r.stdout) if ok else r
    sealed=command(fixture,'seal',label='fixture-seal');pin=sealed['manifest_sha256']
    command(fixture,'verify','--manifest-sha256',pin,label='fixture-verify')
    fail=[]
    def rejected(label,mutate,restore):
        mutate()
        command(fixture,'verify','--manifest-sha256',pin,ok=False,label=label)
        restore();command(fixture,'verify','--manifest-sha256',pin,label=label+'-restored')
        fail.append(label)
    target=fixture/'Research_Report53.tex';raw=target.read_bytes()
    rejected('mutated-byte',lambda:target.write_bytes(raw+b'\n'),lambda:target.write_bytes(raw))
    mode=stat.S_IMODE(target.stat().st_mode)
    rejected('mutated-mode',lambda:target.chmod(0o600),lambda:target.chmod(mode))
    extra=fixture/'unexpected'
    rejected('extra-file',lambda:extra.write_text('x'),lambda:extra.unlink())
    rejected('extra-directory',lambda:extra.mkdir(),lambda:extra.rmdir())
    rejected('symlink-member',lambda:extra.symlink_to(target),lambda:extra.unlink())
    held=out/'held-file'
    rejected('missing-file',lambda:target.rename(held),lambda:held.rename(target))
    command(fixture,'verify','--manifest-sha256','0'*64,ok=False,label='wrong-manifest-pin');fail.append('wrong-manifest-pin')
    command(fixture,'seal',ok=False,label='refuse-reseal');fail.append('refuse-reseal')
    command(fixture,'archive','--manifest-sha256',pin,'--output',fixture/'bad.zip',ok=False,label='in-bundle-archive');fail.append('in-bundle-archive')
    alias=out/'output-alias';alias.symlink_to(out,target_is_directory=True)
    command(fixture,'archive','--manifest-sha256',pin,'--output',alias/'bad.zip',ok=False,label='symlink-output');fail.append('symlink-output')
    z1=out/'first.zip';z2=out/'second.zip'
    a=command(fixture,'archive','--manifest-sha256',pin,'--output',z1,label='archive-a')
    b=command(fixture,'archive','--manifest-sha256',pin,'--output',z2,label='archive-b')
    require(z1.read_bytes()==z2.read_bytes(),'ZIP nondeterminism')
    command(fixture,'archive','--manifest-sha256',pin,'--output',z1,ok=False,label='reused-output');fail.append('reused-output')
    extracted=out/'relocated extraction';extracted.mkdir()
    with zipfile.ZipFile(z1) as archive:
        archive.extractall(extracted)
        for info in archive.infolist():
            (extracted/info.filename).chmod((info.external_attr>>16)&0o777)
    command(extracted,'verify','--manifest-sha256',pin,label='extracted-verify')
    builda=command(extracted,'build-pdf','--manifest-sha256',pin,'--output',out/'pdf-a',label='build-a')
    buildb=command(extracted,'build-pdf','--manifest-sha256',pin,'--output',out/'pdf-b',label='build-b')
    require(builda['pdf_sha256']==buildb['pdf_sha256'],'PDF nondeterminism')
    require(snapshot(root)==before,'Live source changed')
    result={'status':'PASS','checker_sha256':digest(Path(__file__).read_bytes()),'release_tool_sha256':digest((root/'release.py').read_bytes()),'pdf_sha256':builda['pdf_sha256'],'pdf_bytes':builda['pdf_bytes'],'pdf_repetitions_identical':True,'zip_repetitions_identical':True,'archive_member_verification':True,'moved_extraction_verify_and_pdf_build':True,'negative_controls_rejected':fail,'live_source_bytes_modes_mtimes_inventory_preserved':True,'fixture_manifest_is_final_seal':False,'executed':'Only newly authored release.py; no scientific or upstream program executed'}
    (out/'receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':main()
