#!/usr/bin/env python3
"""Replay the delivered finite arithmetic, independent of the working directory.

Python standard library only. This never runs the encoded Turing machine and
does not decide the existence of a solution or the consistency of ZFC.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys

ROOT=Path(__file__).resolve().parent
STEPS=[
    ('coefficients','coefficients/build_coefficients.py'),
    ('coefficients_independent','reviews/audit_coefficients_independent.py'),
    ('quartic','quartic/build_quartic31_62.py'),
    ('positive_build','positive/build_new.py'),
    ('positive_checks','positive/check_new.py'),
    ('signed_build','integers/build_signed.py'),
    ('signed_independent','reviews/audit_signed16.py'),
]
ARTIFACTS=[
    'coefficients/'+name+'.bin' for name in ('beta','K','MC','MF_source')
]+['coefficients/wang943_tiles.json']+[
    'positive/'+family+'_'+kind+'.json'
    for family in ('economical','cancellation1065')
    for kind in ('product','system','shifted_system')
]+[
    'quartic/quartic31_system62.json','quartic/quartic31_sos127.json',
    'integers/generated/signed16.json','integers/generated/signed17.json',
    'integers/generated/INDEX_CONSTANTS.json',
    'integers/generated/INDEX_BOUND_CERTIFICATE.json',
]

def require(ok,message):
    if not ok: raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git_hash(data):
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()

def check_sources():
    source_map=json.loads((ROOT/'sources/SOURCE_MAP.json').read_text())
    for row in source_map['files']:
        path=ROOT/row['local_path'];raw=path.read_bytes()
        require(hashlib.sha256(raw).hexdigest()==row['sha256'],
                'SHA-256 source mismatch: '+row['local_path'])
        require(git_hash(raw)==row['git_blob_sha1'],
                'Pinned Git blob mismatch: '+row['local_path'])
    return len(source_map['files'])

def check_manifest():
    path=ROOT/'MANIFEST.sha256'
    require(path.exists(),'MANIFEST.sha256 is missing.')
    count=0
    for line in path.read_text().splitlines():
        expected,name=line.split('  ',1)
        target=ROOT/name
        require(target.is_file(),'Manifest file missing: '+name)
        require(sha(target)==expected,'Manifest hash mismatch: '+name)
        count+=1
    print('PASS: delivery manifest,',count,'files.')

def check_bindings():
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    require(binding['B']=='2^1064921','Unexpected radix')
    require(binding['audit']['total_raw_bytes']==533099,'Unexpected payload size')
    for row in binding['audit']['files']:
        require(sha(ROOT/'coefficients'/(row['name']+'.bin'))==row['sha256'],
                'Coefficient identity mismatch: '+row['name'])
    indices=json.loads((ROOT/'integers/generated/INDEX_CONSTANTS.json').read_text())
    require(indices['index_exponent']==4269855 and indices['nu']==31,'Wrong Jones index')
    require(indices['b_scale']=='2^(4269856*(5^32+1))','Wrong fixed square radix scale')
    require((ROOT/'integers/signed_section.tex').read_bytes()==
            (ROOT/'sections/signed.tex').read_bytes(),'Signed proof copies disagree')
    expected_ports={'beta':'beta.bin','K0':'K.bin','MC':'MC.bin','MF':'MF_source.bin'}
    for family in ('economical','cancellation1065'):
        for kind in ('product','system','shifted_system'):
            p=json.loads((ROOT/'positive'/(family+'_'+kind+'.json')).read_text())
            require(p['fixed_port_payloads']==expected_ports,'Wrong positive port binding')
    return dict(base=binding['B'],raw_coefficient_bytes=533099,
                index_exponent=4269855,source_quartic_sha256=indices['parent_sha256'])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-manifest',action='store_true',
                        help='verify the delivery byte hashes and exit, without rebuilding')
    args=parser.parse_args()
    require(__debug__,'Do not use python -O: assertions are part of component checks.')
    require(sys.version_info>=(3,10),'Python 3.10 or later is required.')
    if args.check_manifest:
        check_manifest();return
    sources=check_sources()
    print('PASS: authenticated',sources,'source files.',flush=True)
    before={name:sha(ROOT/name) for name in ARTIFACTS}
    out=ROOT/'verification';out.mkdir(exist_ok=True)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    steps=[]
    for name,relative in STEPS:
        run=subprocess.run([sys.executable,'-B',str(ROOT/relative)],
                           cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
        (out/(name+'.log')).write_text(run.stdout)
        if run.returncode:
            print(run.stdout,file=sys.stderr)
            raise RuntimeError('Failed '+relative+'; see verification/'+name+'.log')
        steps.append(dict(script=relative,status='PASS',log=name+'.log'))
        print('PASS:',relative,flush=True)
    after={name:sha(ROOT/name) for name in ARTIFACTS}
    changed=[name for name in ARTIFACTS if before[name]!=after[name]]
    require(not changed,'Regenerated mathematical artifacts differ: '+repr(changed))
    binding=check_bindings()
    receipt=dict(status='PASS',scope='Finite identities, source authentication, and literal artifact reproduction; not a consistency decision.',
        python_requirement='>=3.10, standard library only',
        authenticated_source_files=sources,steps=steps,
        mathematical_artifacts_identical=len(ARTIFACTS),artifact_sha256=after,
        fixed_binding=binding)
    (out/'REPRODUCE.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS:',len(ARTIFACTS),'mathematical artifacts reproduced byte-for-byte.')
    print('Receipt: verification/REPRODUCE.json')

if __name__=='__main__':
    main()
