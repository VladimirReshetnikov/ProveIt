#!/usr/bin/env python3
"""Recover batch163 sources64-67 from committed arrivals and compare placed bytes.
Read-only Git access, new external output only. No verification suite, compiler,
network, checksum-manifest interpretation or line-ending conversion.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,subprocess,sys,zipfile
HOST='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
def require(ok,message):
    if not ok:raise ValueError(message)
def relative(name):
    require(isinstance(name,str)and name and not any(x in name for x in ('\\','\0','\n','\r')),f'Unsafe path {name!r}')
    p=PurePosixPath(name);require(not p.is_absolute()and all(x not in ('.','..')for x in p.parts)and ':'not in p.parts[0]and p.as_posix()==name.rstrip('/'),f'Unsafe path {name!r}');return p

def payloads(raw,package):
    require(hashlib.sha256(raw).hexdigest()==package['archive_sha256'],'Arrival archive identity changed')
    files={};seen=set()
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        for info in z.infolist():
            p=relative(info.filename);require(p.parts[0]==package['wrapper'],'Unexpected wrapper');require(str(p)not in seen,'Duplicate archive member');seen.add(str(p));kind=stat.S_IFMT(info.external_attr>>16);require(kind in(0,stat.S_IFDIR,stat.S_IFREG)and not info.flag_bits&1,'Nonregular or encrypted member')
            if info.is_dir():continue
            require(len(p.parts)>1 and kind!=stat.S_IFDIR,'Invalid file member');data=z.read(info);require(len(data)==info.file_size,'Wrong member size');files[PurePosixPath(*p.parts[1:]).as_posix()]=data
    require(set(files)=={f['delivered']for f in package['files']},'Original inventory differs')
    return files

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--source',type=int,choices=range(64,68));ap.add_argument('--mapping',type=Path,help='Default: maintained host data/intake-163-placement.json');a=ap.parse_args();require(__debug__,'Run without -O')
    repo=a.repo.resolve(strict=True);require(Path(subprocess.check_output(['git','-C',str(repo),'rev-parse','--show-toplevel'],text=True).strip()).resolve()==repo,'--repo must be the worktree root')
    requested=a.output.absolute();require(not requested.exists()and not requested.is_symlink(),'Choose a new nonexistent output');output=requested.resolve();require(not output.is_relative_to(repo),'Output must be external')
    mapping=a.mapping or repo/HOST/'data/intake-163-placement.json';m=json.loads(mapping.read_text());require(m['batch']==163 and {p['local_source']for p in m['manuscripts']}==set(range(64,68)),'Wrong batch mapping');prepared=[]
    for p in m['manuscripts']:
        n=p['local_source']
        if a.source is not None and a.source!=n:continue
        raw=subprocess.check_output(['git','-C',str(repo),'show',p['arrival']+':'+p['archive']]);files=payloads(raw,p);placed=[f for f in m['placements']if f['local_source']==n]
        for f in placed:
            relative(f['delivered']);q=repo.joinpath(*relative(f['target']).parts);require(q.is_file()and not q.is_symlink()and q.resolve().is_relative_to(repo/HOST),'Missing/unsafe placed file: '+str(q));require(q.read_bytes()==files[f['delivered']],'Placed bytes differ: '+str(q))
        prepared.append((p,files,len(placed)))
    output.mkdir(parents=True,exist_ok=False);records=[]
    for p,files,count in prepared:
        root=output/f"{p['local_source']}-{p['slug']}"/p['wrapper']
        for name,data in files.items():
            q=root.joinpath(*relative(name).parts);q.parent.mkdir(parents=True,exist_ok=True)
            with q.open('xb') as out:out.write(data)
        records.append(dict(source=p['local_source'],root=str(root),arrival=p['arrival'],archive=p['archive'],recovered_files=len(files),placed_byte_comparisons=count))
    record=dict(status='RECOVERED_ONLY',packages=records,compiler_invocations=0,test_invocations=0,checksum_manifests_interpreted=False,line_endings_changed=False)
    (output/'recovery.json').write_text(json.dumps(record,indent=2)+'\n')
    for x in records:print(f"source{x['source']}: {x['root']}")
    print('Recovered',sum(x['recovered_files']for x in records),'files; compared',sum(x['placed_byte_comparisons']for x in records),'placed pairs. Record:',output/'recovery.json')
if __name__=='__main__':
    try:main()
    except (OSError,ValueError,zipfile.BadZipFile,subprocess.CalledProcessError)as e:print('Recovery failed:',e,file=sys.stderr);raise SystemExit(1)
