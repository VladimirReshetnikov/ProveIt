#!/usr/bin/env python3
"""Small no-network rejection tests; active under both ordinary Python and -O."""
import json
from pathlib import Path
import tempfile
import build
import verify_manifest


def rejected(call):
    try:
        call()
    except (ValueError,build.BuildError,OSError):
        return
    raise RuntimeError('expected rejection did not occur')


def main():
    count=0
    with tempfile.TemporaryDirectory(prefix='report175-guards-') as tmp:
        root=Path(tmp);keep=root/'keep';keep.mkdir();sentinel=keep/'sentinel';sentinel.write_bytes(b'preserve')
        rejected(lambda:build.build(keep));count+=1
        if sentinel.read_bytes()!=b'preserve':raise RuntimeError('existing output was altered')
        link=root/'link';link.symlink_to(keep,target_is_directory=True)
        rejected(lambda:build.build(link));count+=1
        rejected(lambda:build.safe_source('../escape',root));count+=1
        rejected(lambda:build.safe_source('/absolute',root));count+=1
        rejected(lambda:build.safe_source('a\\b',root));count+=1
        source=root/'source';source.write_text('ok');symlink=root/'sym';symlink.symlink_to(source)
        rejected(lambda:build.safe_source('sym',root));count+=1
        package=root/'package';package.mkdir();payload=package/'x';payload.write_bytes(b'good')
        manifest=package/'SHA256SUMS.json';manifest.write_bytes(build.canonical(build.inventory(package)))
        verify_manifest.verify(package)
        payload.write_bytes(b'bad');rejected(lambda:verify_manifest.verify(package));count+=1
        payload.write_bytes(b'good');extra=package/'extra';extra.write_bytes(b'new')
        rejected(lambda:verify_manifest.verify(package));count+=1;extra.unlink()
        payload.unlink();rejected(lambda:verify_manifest.verify(package));count+=1
        manifest.write_text('{"../escape":"'+('0'*64)+'"}')
        rejected(lambda:verify_manifest.verify(package));count+=1
    print(json.dumps({'status':'PASS','rejection_tests':count},sort_keys=True))

if __name__=='__main__':
    main()
