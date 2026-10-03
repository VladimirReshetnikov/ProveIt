#!/usr/bin/env python3
"""Maintainer-only sealing tool: regenerate inventory and one normalized self-pin.

Do not use this to validate a received release. Use verify_release.py instead.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import stat

ROOT = Path(__file__).resolve().parent
PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--draft',action='store_true',help='explicitly label an engineering preview without the completed article')
    a = p.parse_args()
    if not a.draft:
        require((ROOT/'report32.tex').is_file() and (ROOT/'report32.pdf').is_file(),'Final article TeX and PDF must exist before sealing')
    records = {}
    for path in sorted(ROOT.rglob('*')):
        name = path.relative_to(ROOT).as_posix()
        require(not path.is_symlink(),'Symlinks are forbidden')
        mode = path.stat().st_mode
        require(stat.S_ISDIR(mode) or stat.S_ISREG(mode),'Special paths are forbidden')
        if path.is_dir() or name in ('MANIFEST.json','SHA256SUMS'):
            continue
        require(re.fullmatch(r'[A-Za-z0-9_./-]+',name) is not None and all(x not in ('','.','..') for x in name.split('/')),'Unsafe path')
        require(path.suffix not in ('.pyc','.pyo','.aux','.out','.toc','.fls','.fdb_latexmk') and (path.suffix != '.log' or name in ('core/evidence/check-normal.log','core/evidence/check-optimized.log')),'Generated caches/logs must remain outside release')
        raw = path.read_bytes()
        if name == 'verify_release.py':
            require(len(re.findall(PATTERN,raw)) == 1,'Verifier self-pin line malformed')
            normalized = re.sub(PATTERN,ZERO,raw)
        else:
            normalized = raw
        records[name] = {'bytes':len(raw),'sha256':sha(normalized)}
    manifest = {'schema':'report32-release-inventory-v1','release_stage':'engineering-preview' if a.draft else 'final',
                'files':records,'file_count':len(records),
                'hash_convention':'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact'}
    raw = (json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
    (ROOT/'MANIFEST.json').write_bytes(raw)
    pin = sha(raw)
    script = ROOT/'verify_release.py'
    script.write_bytes(re.sub(PATTERN,b'MANIFEST_SHA256 = "'+pin.encode()+b'"',script.read_bytes()))
    sums = ''.join(sha((ROOT/name).read_bytes())+'  '+name+'\n' for name in sorted(set(records)|{'MANIFEST.json'}))
    (ROOT/'SHA256SUMS').write_text(sums,encoding='utf-8')
    print(json.dumps({'status':'SEALED','release_stage':manifest['release_stage'],'manifest_sha256':pin,'inventory_file_count':len(records)},sort_keys=True))

if __name__ == '__main__':
    main()
