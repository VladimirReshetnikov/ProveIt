"""Read-only safety and embedded-manifest verification for this ZIP format."""
import hashlib,json,stat,sys,zipfile
from pathlib import PurePosixPath
archive=sys.argv[1]
with zipfile.ZipFile(archive) as z:
    infos=z.infolist(); names=[x.filename for x in infos]
    assert len(names)==len(set(names)), 'duplicate archive entries'
    assert len(infos)<=200 and sum(x.file_size for x in infos)<20_000_000, 'unexpected archive size'
    top=set()
    for info in infos:
        name=info.filename; path=PurePosixPath(name)
        assert not path.is_absolute() and '..' not in path.parts and '\\' not in name, name
        assert path.parts and ':' not in path.parts[0], name
        assert not info.is_dir(), 'file-only archive expected'
        mode=info.external_attr >> 16
        assert not stat.S_ISLNK(mode), name
        top.add(path.parts[0])
    assert len(top)==1, 'expected one top-level directory'
    prefix=next(iter(top))+'/'
    manifest=json.loads(z.read(prefix+'MANIFEST.json'))
    assert set(names)=={prefix+p for p in manifest['files']}|{prefix+'MANIFEST.json'}, 'unlisted archive entries'
    for name,meta in manifest['files'].items():
        data=z.read(prefix+name)
        assert len(data)==meta['size'], name
        assert hashlib.sha256(data).hexdigest()==meta['sha256'], name
    print(f'PASS: {len(infos)} safe ZIP members, {len(manifest["files"])} manifest-pinned payload files')
