#!/usr/bin/env python3
"""Restore both original batch168 layouts and compare151 maintained ancillary bytes; execute no supplied code."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,stat,subprocess,zipfile
MAP='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake168-placement.json'
MAP_SHA='b758650ab59a7dff4b49aa20dac26597ff942116cc3fc0a4de40986a14e3a6c8'
def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def safe(name):
    p=PurePosixPath(name)
    require(bool(p.parts) and not p.is_absolute() and '..' not in p.parts and not any(c in name for c in '\\\r\n:'),'Unsafe member')
    return p

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();repo=args.repo.resolve();out=args.output.resolve()
    require(not out.exists() and out!=repo and repo not in out.parents and out not in repo.parents,'Output must be new and outside repository')
    rawmap=(repo/MAP).read_bytes();require(sha(rawmap)==MAP_SHA,'Exact placement map required');p=json.loads(rawmap)
    require(p['sources']==[72,73] and len(p['members'])==163 and p['placed']==151 and p['archive_only']==12,'Census')
    allfiles={};checked=[];archives={}
    for row in p['members']:
        arc=row['archive'];safe(arc)
        if arc not in archives:
            raw=subprocess.check_output(['git','-C',str(repo),'show',p['arrival']+':'+arc]);files={}
            with zipfile.ZipFile(io.BytesIO(raw)) as z:
                require(sum(e.file_size for e in z.infolist())<100_000_000,'Expanded-size cap')
                for e in z.infolist():
                    safe(e.filename);require(not stat.S_ISLNK(e.external_attr>>16),'Symlink member')
                    if e.is_dir():continue
                    require(e.filename not in files,'Repeated member');files[e.filename]=z.read(e)
            expected={r['archive_member'] for r in p['members'] if r['archive']==arc}
            require(set(files)==expected,'Exact archive census');archives[arc]=(raw,files)
        raw,files=archives[arc];data=files[row['archive_member']]
        require(sha(data)==row['sha256'] and blob(data)==row['git_blob'],'Original member identity')
        name=row['archive_member'];require(name not in allfiles,'Cross-archive path collision');allfiles[name]=data
        if row['disposition']=='place_unchanged':
            dest=repo.joinpath(*safe(row['target']).parts)
            require(repo in dest.resolve().parents and dest.read_bytes()==data,'Maintained ancillary differs')
            checked.append(row['target'])
        else:require(row['disposition']=='archive_only','Disposition')
    require(len(checked)==len(set(checked))==151,'Ancillary census')
    out.mkdir()
    for name,data in allfiles.items():
        dest=out.joinpath(*safe(name).parts);dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
    result={'status':'ORIGINAL_LAYOUT_RECOVERED_AND_PLACED_BYTES_MATCH','members':163,'placed':151,'archive_only':12,'map_sha256':MAP_SHA,'output':str(out),'supplied_execution':False,'checksum_manifest_validation':False}
    (out/'recovery.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
