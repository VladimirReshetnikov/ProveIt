#!/usr/bin/env python3
"""Portable combined audit. Python standard library only; no assertions used.

The universal semantic proofs are in report/report.tex and the component proofs.
This driver verifies finite algebra/data claims and replays both components.
"""
from __future__ import annotations
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def require(value, message):
    if not value:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def authenticate_manifest():
    path = ROOT / 'MANIFEST.sha256'
    require(path.is_file(), 'Missing MANIFEST.sha256')
    entries = {}
    for line in path.read_text().splitlines():
        sha, rel = line.split('  ', 1)
        require(rel not in entries, 'Duplicate manifest path: ' + rel)
        require(not Path(rel).is_absolute() and '..' not in Path(rel).parts,
                'Unsafe manifest path: ' + rel)
        entries[rel] = sha
        require(digest(ROOT / rel) == sha, 'Archive file hash mismatch: ' + rel)
    return len(entries)


def authenticate_sources():
    locations = [
        (ROOT / 'integer/SOURCE_PINS.json', ROOT / 'integer'),
        (ROOT / 'positive/SOURCE_PINS.json', ROOT / 'positive'),
        (ROOT / 'positive/native/SOURCE_PINS.json', ROOT / 'positive/native'),
        (ROOT / 'review/SOURCE_PINS.json', ROOT),
    ]
    count = 0
    for manifest, base in locations:
        doc = json.loads(manifest.read_text())
        for entry in doc['files']:
            data = (base / entry['local']).read_bytes()
            git_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            expected = entry.get('git_blob_sha1', entry.get('git_blob'))
            require(git_sha == expected, 'Pinned Git blob mismatch: ' + entry['local'])
            if 'sha256' in entry:
                require(hashlib.sha256(data).hexdigest() == entry['sha256'],
                        'Pinned SHA256 mismatch: ' + entry['local'])
            count += 1
    return count


def paper_quartic():
    """Independent translation of the 25 displayed rows in report Section 4."""
    path = ROOT / 'integer/reproduce.py'
    spec = importlib.util.spec_from_file_location('cone_sparse_ring', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    packet = json.loads((ROOT / 'integer/quartic38.json').read_text())
    symbols = {name: module.P.var(name) for name in packet['variables'] + packet['fixed_numerals']}
    names = ['J','F','alpha','z','f','h','r','v_scale','w_scale','tau','eta','zeta','y','gamma','o','j',
             'N','E','P','c','a','X','D','C2','L','F2','V','g','I','Baux','Delta','u',
             'eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3','cone1','cone2','cone3',
             'beta','K0','MC','MF','Walpha','WC']
    (J,F,alpha,z,f,h,r,v,w,tau,eta,zeta,y,gamma,o,j,
     N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta,u,s1,s2,s3,e1,e2,e3,
     beta,K0,MC,MF,Walpha,WC) = (symbols[name] for name in names)
    q = beta*J+1
    C = q-F-alpha
    k = eta+zeta
    Rhat = (q-F)*(N-L-q)+alpha*L+(MC+q*MF)*J
    pos = lambda a,b,c: 1+a*a+b*b+c*(c+1)
    cone = lambda a,b,c: 2*(a*b+a*c+b*c)-a*a-b*b-c*c
    rows = [
        L-q*q+1, N-q*(L+1), X-4*q*w, a-E-(2*v+1)*N,
        E*X+E-X*a, c-eta-k*(a-E), P-k-E*(c-eta), tau*tau-P*P+P*k-1,
        D-X-a*c-gamma*(4*a+3), Delta-a*a-4*a-3, C2-c*c, D*D-Delta*C2-1,
        k-Rhat-1-E*h, (K0+4*w)*C-F-(q-1)*z, F2-f*f, V+c-f*o,
        V-c*j+k-1-E*h, V*V+g-y*y, I-(2*r+1)*C2, Baux-I*I,
        Baux-Delta*F2+Delta, -Baux*g+y*y-1, X-2*u*u,
        eta*zeta-pos(s1,s2,s3), cone(beta*F,Walpha*alpha,WC*C)-pos(e1,e2,e3),
    ]
    require(len(rows) == len(packet['residuals']) == 25, 'Paper quartic row count')
    for index, (row, text) in enumerate(zip(rows, packet['residuals']), 1):
        require(row == module.parse(text), 'Paper quartic transcription: row ' + str(index))
    return {'residuals_checked': 25, 'status': 'PASS'}


def run_components():
    results = {}
    flags = ['-O'] if not __debug__ else []
    with tempfile.TemporaryDirectory(prefix='con-zfc-combined-') as temporary:
        stage = Path(temporary)
        for component, entrypoint in [('integer', 'reproduce.py'), ('positive', 'verify.py')]:
            work = stage / component
            shutil.copytree(ROOT / component, work)
            env = dict(os.environ)
            env['PYTHONDONTWRITEBYTECODE'] = '1'
            command = [sys.executable] + flags + [str(work / entrypoint)]
            print('Checking ' + component + ' in an isolated copy...', flush=True)
            completed = subprocess.run(command, cwd=work, env=env, capture_output=True, text=True)
            if completed.returncode:
                sys.stderr.write(completed.stdout)
                sys.stderr.write(completed.stderr)
                raise RuntimeError(component + ' audit failed')
            receipt_path = work / ('CHECKS.json' if component == 'integer' else
                                  'certificates/' + ('CHECKS_OPTIMIZED.json' if flags else 'CHECKS.json'))
            receipt = json.loads(receipt_path.read_text())
            if component == 'integer':
                for name in ['quartic38.json', 'sextic32.json', 'octic27.json']:
                    require((work/name).read_bytes() == (ROOT/component/name).read_bytes(),
                            'Byte-identical rebuilt integer equation: ' + name)
            results[component] = {'status': 'PASS', 'receipt': receipt}
            print(component + ': PASS', flush=True)
    return results


def main():
    count = authenticate_manifest()
    sources = authenticate_sources()
    transcription = paper_quartic()
    components = run_components()
    result = {
        'status': 'PASS',
        'python': sys.version.split()[0],
        'optimized': not __debug__,
        'manifest_files_authenticated': count,
        'pinned_source_files_authenticated_by_root': sources,
        'paper_quartic_transcription': transcription,
        'components': components,
        'scope': 'Exact finite algebra, coefficient, provenance and reproduction checks. '
                 'Universal new proofs and inherited semantic interfaces are in the paper and component proofs.',
    }
    (ROOT / 'VERIFICATION.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('PASS: archive integrity, source pins, paper transcription, and both component audits.', flush=True)
    print('Detailed receipt: VERIFICATION.json', flush=True)


if __name__ == '__main__':
    main()
