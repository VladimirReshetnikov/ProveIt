#!/usr/bin/env python3
"""Check bundle inventory, digests and selected immutable source bytes; execute nothing."""
import argparse,hashlib,json,pathlib,stat,sys,zipfile
MANIFEST='MANIFEST.sha256.json'

def verify(path):
    with zipfile.ZipFile(path) as z:
        entries=z.infolist(); names=[i.filename for i in entries]
        if len(names)!=len(set(names)): raise ValueError('duplicate ZIP member')
        for i in entries:
            p=pathlib.PurePosixPath(i.filename)
            if p.is_absolute() or '..' in p.parts or '\\' in i.filename or str(p)!=i.filename or i.is_dir() or stat.S_ISLNK(i.external_attr>>16):
                raise ValueError('unsafe or non-file ZIP member: '+i.filename)
        if sum(i.file_size for i in entries)>12_000_000:raise ValueError('excessive expanded size')
        manifest=json.loads(z.read(MANIFEST));expected=manifest['files']
        if set(names)!=set(expected)|{MANIFEST}:raise ValueError('member inventory mismatch')
        for name,meta in expected.items():
            b=z.read(name)
            if len(b)!=meta['bytes']:raise ValueError('length mismatch: '+name)
            if hashlib.sha256(b).hexdigest()!=meta['sha256']:raise ValueError('SHA-256 mismatch: '+name)
        selected=json.loads(z.read('evidence/selected_sources.json'))
        if selected['pin']!=manifest['source_pin']:raise ValueError('source pin mismatch')
        for rec in selected['files']:
            b=z.read(rec['bundle_path'])
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if len(b)!=rec['bytes'] or blob!=rec['git_blob'] or hashlib.sha256(b).hexdigest()!=rec['sha256']:
                raise ValueError('source provenance mismatch: '+rec['bundle_path'])
        return {'status':'PASS','payload_files':len(expected),'selected_sources_verified':len(selected['files']),
          'uncompressed_bytes':sum(i.file_size for i in entries),'archive_bytes':pathlib.Path(path).stat().st_size,
          'archive_sha256':hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('archive');a=p.parse_args()
    try:print(json.dumps(verify(a.archive),indent=2))
    except (ValueError,KeyError,zipfile.BadZipFile,json.JSONDecodeError) as e:
        print('FAIL: '+str(e),file=sys.stderr);return 1
    return 0
if __name__=='__main__':sys.exit(main())
