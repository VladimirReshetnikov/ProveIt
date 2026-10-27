#!/usr/bin/env python3
"""Verify the sealed archive and selected-source evidence; execute nothing."""
import argparse,hashlib,json,pathlib,stat,sys,zipfile
MANIFEST='MANIFEST.sha256.json'

def verify(path):
    path=pathlib.Path(path)
    if path.stat().st_size>=4_000_000:raise ValueError('archive must be below 4 MB')
    with zipfile.ZipFile(path) as z:
        entries=z.infolist();names=[i.filename for i in entries]
        if len(names)!=len(set(names)):raise ValueError('duplicate ZIP member')
        for i in entries:
            p=pathlib.PurePosixPath(i.filename)
            if p.is_absolute() or '..' in p.parts or '\\' in i.filename or str(p)!=i.filename or i.is_dir() or stat.S_ISLNK(i.external_attr>>16):raise ValueError('unsafe member')
        if sum(i.file_size for i in entries)>16_000_000:raise ValueError('excessive expansion')
        manifest=json.loads(z.read(MANIFEST));expected=manifest['files']
        if set(names)!=set(expected)|{MANIFEST}:raise ValueError('member inventory mismatch')
        for name,meta in expected.items():
            b=z.read(name)
            if len(b)!=meta['bytes'] or hashlib.sha256(b).hexdigest()!=meta['sha256']:raise ValueError('payload hash mismatch: '+name)
        selected=json.loads(z.read('evidence/selected_sources.json'))
        if selected['pin']!=manifest['source_pin']:raise ValueError('source pin mismatch')
        canonical=0
        for rec in selected['files']:
            b=z.read(rec['bundle_path'])
            if len(b)!=rec['bytes'] or hashlib.sha256(b).hexdigest()!=rec['sha256']:raise ValueError('selected-source mismatch')
            if 'git_blob' in rec:
                blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
                if blob!=rec['git_blob']:raise ValueError('source Git-blob mismatch')
                canonical+=1
        return {'status':'PASS','payload_files':len(expected),'selected_sources_verified':len(selected['files']),
                'canonical_git_blobs_verified':canonical,'uncompressed_bytes':sum(i.file_size for i in entries),
                'archive_bytes':path.stat().st_size,'archive_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                'provenance_scope':'Retained acquisition evidence; no network or fresh source archive re-download.'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('archive');a=p.parse_args()
    try: print(json.dumps(verify(a.archive),indent=2))
    except (ValueError,KeyError,zipfile.BadZipFile,json.JSONDecodeError) as e:
        print('FAIL: '+str(e),file=sys.stderr);return 1
    return 0
if __name__=='__main__':sys.exit(main())
