#!/usr/bin/env python3
"""Maintainer-only Report40 sealer. Never reseal a received package to validate it.

Use --engineering-preview only on disposable QA copies. Final sealing requires
an exact-article approval record and passing original-source replay. Obtain the
published archive digest independently before executing a received package.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import stat
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PATTERN = rb'(?m)^MANIFEST_SHA256 = "[0-9a-f]{64}"$'
ZERO = b'MANIFEST_SHA256 = "'+b'0'*64+b'"'


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument('--final',action='store_true')
    g.add_argument('--engineering-preview',action='store_true')
    a = p.parse_args()
    # This maintainer operation necessarily trusts these local helper bytes.
    # Source programs are only read, hashed and parsed; none is imported.
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('report40_verifier',ROOT/'verify_release.py')
    verifier = importlib.util.module_from_spec(spec);spec.loader.exec_module(verifier)
    verifier.snapshot(ROOT)
    verifier.verify_source(ROOT)
    if a.final:
        need(all((ROOT/name).is_file() for name in ('Research_Report40.tex','Research_Report40.pdf')), 'Final article is missing')
        verifier.verify_approval(ROOT)
    entries = {}
    ROOT.chmod(0o755)
    for path in sorted(ROOT.rglob('*')):
        name = path.relative_to(ROOT).as_posix()
        need(not path.is_symlink(), 'Symlinks are forbidden')
        mode = path.stat().st_mode
        need(stat.S_ISREG(mode) or stat.S_ISDIR(mode), 'Special files are forbidden')
        verifier.safe_relative(name)
        if path.is_dir():
            path.chmod(0o755);continue
        if not name.startswith(verifier.SOURCE_PREFIX):
            need(path.suffix not in ('.pyc','.pyo','.aux','.out','.toc','.fls','.fdb_latexmk','.log') and '__pycache__' not in path.parts, 'Caches and generated QA must be external')
        path.chmod(0o644)
        if name in ('MANIFEST.json','SHA256SUMS'):continue
        raw = path.read_bytes()
        normalized = verifier.normalized_verifier(raw) if name == 'verify_release.py' else raw
        entries[name] = {'bytes':len(raw),'sha256':sha(normalized),'mode':0o644}
    doc = {'schema':'report40-release-inventory-v1','release_stage':'final' if a.final else 'engineering-preview','file_count':len(entries),'hash_convention':verifier.HASH_CONVENTION,'files':entries}
    raw = (json.dumps(doc,indent=2,sort_keys=True)+'\n').encode()
    (ROOT/'MANIFEST.json').write_bytes(raw)
    pin = sha(raw)
    path = ROOT/'verify_release.py'
    path.write_bytes(re.sub(PATTERN,b'MANIFEST_SHA256 = "'+pin.encode()+b'"',path.read_bytes()))
    sums = ''.join(sha((ROOT/n).read_bytes())+'  '+n+'\n' for n in sorted(set(entries)|{'MANIFEST.json'}))
    (ROOT/'SHA256SUMS').write_text(sums,encoding='utf-8')
    (ROOT/'MANIFEST.json').chmod(0o644);(ROOT/'SHA256SUMS').chmod(0o644)
    checked = subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify_release.py'),'--verify-only'],capture_output=True,text=True,timeout=120)
    need(checked.returncode == 0, 'Sealed tree failed its identity gate: '+checked.stderr[-3000:])
    print(json.dumps({'schema':'report40-seal-v1','status':'SEALED','release_stage':doc['release_stage'],'manifest_sha256':pin,'verifier_sha256':sha(path.read_bytes()),'payload_files':len(entries)},indent=2,sort_keys=True))


if __name__ == '__main__':main()
