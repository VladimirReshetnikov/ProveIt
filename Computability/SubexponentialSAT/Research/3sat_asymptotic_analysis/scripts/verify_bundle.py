#!/usr/bin/env python3
"""Validate a sealed research ZIP without executing its contents.

The manifest establishes internal consistency, not publisher authenticity.
An independently communicated SHA-256 of the whole archive is the trust anchor.
"""
import argparse, hashlib, json, pathlib, stat, sys, zipfile

MANIFEST = 'MANIFEST.sha256.json'
MAX_TOTAL = 12_000_000

def verify(path):
    with zipfile.ZipFile(path) as z:
        entries = z.infolist()
        names = [i.filename for i in entries]
        if len(names) != len(set(names)):
            raise ValueError('duplicate ZIP member')
        for i in entries:
            p = pathlib.PurePosixPath(i.filename)
            if (p.is_absolute() or '..' in p.parts or '\\' in i.filename
                    or str(p) != i.filename or i.is_dir()
                    or stat.S_ISLNK(i.external_attr >> 16)):
                raise ValueError('unsafe or non-file ZIP member: ' + i.filename)
        if sum(i.file_size for i in entries) > MAX_TOTAL:
            raise ValueError('archive expands beyond permitted evidence size')
        manifest = json.loads(z.read(MANIFEST))
        expected = manifest['files']
        if set(names) != set(expected) | {MANIFEST}:
            raise ValueError('member inventory differs from manifest')
        for name, meta in expected.items():
            content = z.read(name)
            if len(content) != meta['bytes']:
                raise ValueError('length mismatch: ' + name)
            if hashlib.sha256(content).hexdigest() != meta['sha256']:
                raise ValueError('SHA-256 mismatch: ' + name)
        source_files=0
        for meta_path,prefix,field in [('source/manifest.json','source/','path'),
                    ('audit/lean_selected/manifest.json','audit/lean_selected/','local_file')]:
            provenance=json.loads(z.read(meta_path))
            if provenance['pin'] != manifest['source_pin']:
                raise ValueError('source pin mismatch: '+meta_path)
            for record in provenance['files']:
                name=prefix+record[field]; content=z.read(name)
                blob=hashlib.sha1(b'blob '+str(len(content)).encode()+bytes([0])+content).hexdigest()
                if (len(content)!=record['bytes'] or blob!=record['git_blob']
                        or hashlib.sha256(content).hexdigest()!=record['sha256']):
                    raise ValueError('source provenance mismatch: '+name)
                source_files+=1
        return {'status': 'PASS', 'source_files_verified':source_files, 'payload_files': len(expected),
                'uncompressed_bytes': sum(i.file_size for i in entries),
                'archive_bytes': pathlib.Path(path).stat().st_size,
                'archive_sha256': hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()}

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('archive')
    a=p.parse_args()
    try: print(json.dumps(verify(a.archive), indent=2))
    except (ValueError, KeyError, zipfile.BadZipFile, json.JSONDecodeError) as e:
        print('FAIL: '+str(e), file=sys.stderr); return 1
    return 0
if __name__ == '__main__': sys.exit(main())
