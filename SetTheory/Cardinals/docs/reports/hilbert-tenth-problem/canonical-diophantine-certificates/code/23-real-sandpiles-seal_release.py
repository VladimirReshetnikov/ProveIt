#!/usr/bin/env python3
"""Maintainer sealing utility. Never use it to validate a received release.

This changes the manifest and verifier pin. A published digest must be obtained
independently; an attacker who can replace the verifier can replace its pins.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import stat
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO = b'MANIFEST_SHA256 = "' + b'0'*64 + b'"'


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--final',action='store_true',help='seal only after the final article and approved packets are installed')
    g.add_argument('--engineering-preview',action='store_true',help='for a disposable QA copy only')
    a = p.parse_args()
    if a.final:
        need(all((ROOT/name).is_file() for name in ('Research_Report36.tex','Research_Report36.pdf')),'Final article is missing')
        review = json.loads((ROOT/'verification/release-review.json').read_bytes())
        need(type(review) is dict and review.get('schema') == 'report36-release-review-v1' and review.get('status') == 'APPROVED','Release approval is missing')
        need(review.get('source_manifest_sha256') == '99e4371291d46d7ee8ef4821254ad702791e9b84060e69336d652e603c059ee1' and review.get('source_base_compiler_sha256') == 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2','Release approval identifies a different source')
    entries = {}
    ROOT.chmod(0o755)
    for path in sorted(ROOT.rglob('*')):
        name = path.relative_to(ROOT).as_posix()
        need(not path.is_symlink(),'Symlinks are forbidden')
        mode = path.stat().st_mode
        need(stat.S_ISREG(mode) or stat.S_ISDIR(mode),'Special files are forbidden')
        need(re.fullmatch(r'[A-Za-z0-9_./-]+',name) is not None and all(v not in ('','.','..') for v in name.split('/')),'Unsafe inventory path')
        if path.is_dir():
            path.chmod(0o755)
            continue
        need((path.suffix not in ('.pyc','.pyo','.aux','.out','.toc','.fls','.fdb_latexmk','.log')) and '__pycache__' not in path.parts,'Caches and build outputs must be external')
        path.chmod(0o644)
        if name in ('MANIFEST.json','SHA256SUMS'):continue
        raw = path.read_bytes()
        if name == 'verify_release.py':
            need(len(re.findall(PATTERN,raw)) == 1,'Verifier pin line malformed')
            normalized = re.sub(PATTERN,ZERO,raw)
        else:normalized = raw
        entries[name] = {'bytes':len(raw),'sha256':sha(normalized),'mode':0o644}
    doc = {'schema':'report36-release-inventory-v1','release_stage':'final' if a.final else 'engineering-preview','file_count':len(entries),'hash_convention':'sha256; verify_release.py self-pin line normalized to 64 zeros; all other files byte-exact','files':entries}
    raw = (json.dumps(doc,indent=2,sort_keys=True)+'\n').encode()
    (ROOT/'MANIFEST.json').write_bytes(raw)
    pin = sha(raw)
    verifier = ROOT/'verify_release.py'
    verifier.write_bytes(re.sub(PATTERN,b'MANIFEST_SHA256 = "'+pin.encode()+b'"',verifier.read_bytes()))
    sums = ''.join(sha((ROOT/n).read_bytes())+'  '+n+'\n' for n in sorted(set(entries)|{'MANIFEST.json'}))
    (ROOT/'SHA256SUMS').write_text(sums,encoding='utf-8')
    (ROOT/'MANIFEST.json').chmod(0o644);(ROOT/'SHA256SUMS').chmod(0o644)
    checked = subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify_release.py'),'--verify-only'],text=True,capture_output=True,timeout=120)
    need(checked.returncode == 0,'Sealed tree failed its identity gate: '+checked.stderr[-3000:])
    print(json.dumps({'status':'SEALED','release_stage':doc['release_stage'],'manifest_sha256':pin,'verifier_sha256':sha(verifier.read_bytes()),'payload_files':len(entries)},indent=2,sort_keys=True))


if __name__ == '__main__':main()
