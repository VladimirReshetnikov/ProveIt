#!/usr/bin/env python3
"""Materialize the shared-CRT prime-power-lift variant in a separate candidate.

Only the inspected authored direct compiler is used.  No original release,
inherited program, native emitter, Lean file, or old candidate is changed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
DEST = ROOT/'candidates/shared-crt-prime-lift'
ARCHIVE = REPO/'docs/incoming/ConZFC_Shared_Certificates_2026-10-24.zip'
PIN = '61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1'
NAMES = ['build_equation.py','direct_calculus.py','wire_eliminated_source.json',
         'affine_shared_step.json','check_equation.py','audit_power_graph.py',
         'audit_calculus.py']


def need(ok,text):
    if not ok:raise RuntimeError(text)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def prepare(home):
    need(sha(ARCHIVE.read_bytes()) == PIN,'actual whole incoming archive')
    source = home/'source';source.mkdir(parents=True,exist_ok=True)
    pins = {}
    with zipfile.ZipFile(ARCHIVE) as z:
        for name in NAMES:
            raw = z.read('con_zfc_shared_certificates/direct/'+name)
            old = raw
            if name == 'build_equation.py':
                changes = [(b'    V = b.add(m, U)\n',b'    V = U  # Independent private-coordinate bound; prime-power CRT lift.\n'),
                           (b'    H = b.sum([ep, fp, t, V, ONE])\n',b'    H = b.sum([ep, fp, t])  # No local factorial cancellation is needed.\n')]
                for before,after in changes:
                    need(raw.count(before) == 1,'one literal source edit')
                    raw = raw.replace(before,after)
            (source/name).write_bytes(raw)
            pins[name] = dict(original_sha256=sha(old),candidate_sha256=sha(raw),
                              original_member='con_zfc_shared_certificates/direct/'+name)
        (home/'LICENSE.upstream').write_bytes(z.read('con_zfc_shared_certificates/LICENSE'))
    (home/'SOURCE_PINS.json').write_text(json.dumps(dict(archive=str(ARCHIVE.relative_to(REPO)),archive_sha256=PIN,
        changes=['Private coordinate bounds m+U become U; label bounds remain m.',
                 'Factorial argument E(t,u)+F(t,u)+t+V+1 becomes E(t,u)+F(t,u)+t.'],
        files=pins),indent=2)+'\n')
    return source


def generate(home):
    source=prepare(home)
    for folder,flags in [('affine',[]),('retained',['--keep-linear-wires'])]:
        cmd=[sys.executable,'-B',str(source/'build_equation.py'),*flags,'--output',str(home/folder)]
        subprocess.run(cmd,capture_output=True,text=True,check=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    if args.check:
        with tempfile.TemporaryDirectory(prefix='proveit-shared-crt-lift-') as tmp:
            fresh=Path(tmp);generate(fresh)
            for path in fresh.rglob('*'):
                if path.is_file() and '__pycache__' not in path.parts:
                    old=DEST/path.relative_to(fresh)
                    need(old.exists() and old.read_bytes()==path.read_bytes(),'deterministic '+str(path.relative_to(fresh)))
    else:
        DEST.mkdir(parents=True,exist_ok=True);generate(DEST)
    summary={name:json.loads((DEST/name/'BUILD.json').read_text())['metrics'] for name in ['affine','retained']}
    print(json.dumps(dict(status='PASS',check=args.check,variants=summary),indent=2))


if __name__=='__main__':main()
