#!/usr/bin/env python3
"""Report 53 integrity, deterministic offline PDF build, and deterministic ZIP.

Only this release tool and the separate pinned replay adapter are entry points.
Use Python -I, without -O. All outputs except author-time seal are fresh and
outside the release. No scientific builder, schedule, or Lean file is run.
"""
import sys
if not sys.flags.isolated or sys.flags.optimize:
    raise SystemExit('Run with python3 -I and without -O')
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import zipfile

ROOT=Path(__file__).resolve().parent
NAME='Research_Report53'
EPOCH='1791072000'
MANIFEST='MANIFEST.json'

def need(ok,message):
    if not ok: raise RuntimeError(message)

def sha(data): return hashlib.sha256(data).hexdigest()

def emit(data): print(json.dumps(data,sort_keys=True,indent=2))

def tree(root,temporal=False):
    result={}
    for p in [root]+sorted(root.rglob('*')):
        info=p.lstat(); key='.' if p==root else p.relative_to(root).as_posix()
        need(stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode),'Nonregular entry: '+key)
        row={'kind':'directory' if p.is_dir() else 'file','mode':stat.S_IMODE(info.st_mode)}
        if p.is_file(): row.update(size=info.st_size,sha256=sha(p.read_bytes()))
        if temporal: row['mtime_ns']=info.st_mtime_ns
        result[key]=row
    return result

def new_output(raw,kind):
    p=raw.absolute()
    for part in [p]+list(p.parents): need(not part.is_symlink(),'Symlink output path')
    need(not p.exists(),'Output already exists')
    need(p.parent.is_dir(),'Output parent must exist')
    p=p.resolve()
    need(p!=ROOT and ROOT not in p.parents and p not in ROOT.parents,'Output overlaps release')
    if kind=='zip': need(p.suffix=='.zip','Archive output must end in .zip')
    return p

def verify(pin):
    path=ROOT/MANIFEST
    need(path.is_file() and not path.is_symlink(),'Missing regular manifest')
    need(pin is not None and len(pin)==64,'Supply independently trusted --manifest-sha256')
    need(sha(path.read_bytes())==pin,'Manifest SHA256 mismatch')
    data=json.loads(path.read_text())
    need(data.get('schema')=='report53-release-manifest-v1','Unexpected manifest schema')
    actual=tree(ROOT)
    need(actual[MANIFEST]['mode']==0o644,'Manifest mode mismatch')
    del actual[MANIFEST]
    need(actual==data['entries'],'Inventory, bytes, or modes differ from manifest')
    return {'status':'PASS','manifest_sha256':pin,'entries_verified':len(actual),'exact_inventory':True}

def run(cmd,cwd,env,log):
    with log.open('wb') as stream:
        completed=subprocess.run(cmd,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=300)
    need(completed.returncode==0,'Command failed; inspect '+str(log))

def build(args):
    out=new_output(args.output,'directory')
    before=tree(ROOT,True)
    if not args.draft: verify(args.manifest_sha256)
    out.mkdir()
    shutil.copyfile(ROOT/(NAME+'.tex'),out/(NAME+'.tex'))
    cache=out/'tex-cache';cache.mkdir()
    env=dict(os.environ)
    env.update(TZ='UTC',SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',TEXMFVAR=str(cache),TEXMFCONFIG=str(cache),TEXFORMATS=str(cache)+':')
    def lookup(name):
        x=subprocess.run(['kpsewhich',name],cwd=out,env=env,capture_output=True,text=True,timeout=30)
        return x.stdout.strip() if x.returncode==0 else ''
    if not lookup('article.cls'): env['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    if not lookup('pdflatex.fmt'):
        run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env,cache/'format.log')
    if not lookup('pdftex.map'):
        maps=[]
        for name in ['lm.map','cm.map','cmextra.map','symbols.map','latxfont.map']:
            loc=lookup(name);need(bool(loc),'Missing local font map: '+name)
            maps.append(Path(loc).read_bytes())
        (cache/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
        env['TEXFONTMAPS']=str(cache)+':'
    tex=r'\pdfinfoomitdate=1\pdftrailerid{}\input{'+NAME+'.tex}'
    for i in range(1,4):
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname='+NAME,tex],out,env,out/f'compile-{i}.log')
    pdf=out/(NAME+'.pdf');need(pdf.is_file(),'No PDF produced')
    need(tree(ROOT,True)==before,'Build modified the release')
    identical=(ROOT/pdf.name).is_file() and (ROOT/pdf.name).read_bytes()==pdf.read_bytes()
    if not args.draft: need(identical,'Rebuilt PDF differs from packaged PDF')
    emit({'status':'PASS','pdf_sha256':sha(pdf.read_bytes()),'pdf_bytes':pdf.stat().st_size,'packaged_pdf_identical':identical,'release_bytes_modes_mtimes_unchanged':True,'shell_escape':False,'source_date_epoch':int(EPOCH),'pdflatex':subprocess.run(['pdflatex','--version'],capture_output=True,text=True).stdout.splitlines()[0]})

def archive(args):
    out=new_output(args.output,'zip');before=tree(ROOT,True)
    verification=verify(args.manifest_sha256)
    inventory=tree(ROOT)
    with zipfile.ZipFile(out,'x',compression=zipfile.ZIP_STORED,allowZip64=True) as z:
        for rel,row in sorted(inventory.items()):
            if rel=='.':continue
            isdir=row['kind']=='directory';name=rel+'/' if isdir else rel
            entry=zipfile.ZipInfo(name,date_time=(2026,10,4,0,0,0))
            entry.create_system=3; entry.compress_type=zipfile.ZIP_STORED
            mode=row['mode']|(stat.S_IFDIR if isdir else stat.S_IFREG)
            entry.external_attr=(mode<<16)|(0x10 if isdir else 0)
            z.writestr(entry,b'' if isdir else (ROOT/rel).read_bytes())
    with zipfile.ZipFile(out) as z:
        need(z.testzip() is None,'Archive CRC failure')
        for entry in z.infolist():
            if not entry.is_dir(): need(z.read(entry.filename)==(ROOT/entry.filename).read_bytes(),'Archive member mismatch')
    need(tree(ROOT,True)==before,'Archive creation modified release')
    emit({'status':'PASS','zip_sha256':sha(out.read_bytes()),'zip_bytes':out.stat().st_size,'compression':'ZIP_STORED','timestamp':'2026-10-04T00:00:00','manifest_sha256':args.manifest_sha256,'release_bytes_modes_mtimes_unchanged':True,'members':len(inventory)-1})

def seal():
    need(not (ROOT/MANIFEST).exists(),'Seal exists; do not overwrite it')
    snapshot=tree(ROOT)
    payload={'schema':'report53-release-manifest-v1','date':'2026-10-04','entries':snapshot,'convention':'Manifest excludes itself; its trusted SHA256 must be kept outside the archive. Exact inventory, file bytes, and POSIX modes are verified.'}
    path=ROOT/MANIFEST
    path.write_text(json.dumps(payload,sort_keys=True,indent=2)+'\n');path.chmod(0o644)
    # Directory mtime is intentionally absent from portable integrity metadata.
    pin=sha(path.read_bytes());verify(pin)
    emit({'status':'PASS','manifest_sha256':pin,'entries':len(snapshot)})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest='command',required=True)
    v=commands.add_parser('verify');v.add_argument('--manifest-sha256',required=True)
    b=commands.add_parser('build-pdf');b.add_argument('--output',type=Path,required=True);b.add_argument('--manifest-sha256');b.add_argument('--draft',action='store_true',help='Author-time only: permit an unsealed draft')
    a=commands.add_parser('archive');a.add_argument('--output',type=Path,required=True);a.add_argument('--manifest-sha256',required=True)
    commands.add_parser('seal',help='Author-time only: write first manifest, never overwrite')
    args=parser.parse_args()
    if args.command=='verify':emit(verify(args.manifest_sha256))
    elif args.command=='build-pdf':build(args)
    elif args.command=='archive':archive(args)
    else:seal()
if __name__=='__main__': main()
