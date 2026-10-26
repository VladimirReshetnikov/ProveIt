#!/usr/bin/env python3
"""Offline finite verification of the release. This is not a consistency proof.

All checkers use exact integer/rational arithmetic and the Python standard
library. The ordinary unbounded proof and inherited calibration are identified
in the report. No network, prover installation, or search for roots is used.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
PYTHON=[sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
EXPECTED={
 'source/parent225/equation.json':'fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56',
 'source/anchor221/equation.json':'4024d913bde43aa47e8be1fe8c4f36f560420e8b5ceef999d1625e2e31c31c3e',
 'equations/principal/equation.json':'8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6',
 'equations/companions/p213/equation.json':'9a16fcdcea6310c01236ce500f753034f4095c1956b488f9fd8325b1ceeb89c6',
 'equations/companions/p214/equation.json':'8255b339ce3b76e24024f10aab12114dcfe5ad322c56f3e8eb8c78e2731f0d9f',
}

def need(ok,message):
    if not ok:raise ValueError(message)

def read(path):return json.loads((ROOT/path).read_text())

def run(script,*args):
    p=subprocess.run(PYTHON+[str(ROOT/script)]+[str(a) for a in args],cwd=ROOT,
                     capture_output=True,text=True)
    if p.returncode:
        raise RuntimeError(f'{script} failed ({p.returncode})\n{p.stdout}\n{p.stderr}')
    return json.loads(p.stdout)

def sanitize(value,temp):
    if isinstance(value,dict):return {k:sanitize(v,temp) for k,v in value.items()}
    if isinstance(value,list):return [sanitize(v,temp) for v in value]
    if isinstance(value,str):return value.replace(str(ROOT)+'/','').replace(str(temp),'<temporary-rebuild>')
    return value

def integrity(skip):
    for path,digest in EXPECTED.items():
        need(hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,'Frozen coefficient file changed: '+path)
    pins=read('inherited/SOURCE_BYTE_PINS.json')['files']
    for pin in pins:
        raw=(ROOT/'inherited'/pin['local']).read_bytes()
        need(len(raw)==pin['bytes'],'Copied source length mismatch: '+pin['local'])
        need(hashlib.sha256(raw).hexdigest()==pin['sha256'],'Copied source SHA-256 mismatch: '+pin['local'])
        blob=b'blob '+str(len(raw)).encode()+b'\0'+raw
        need(hashlib.sha1(blob).hexdigest()==pin['git_blob_sha1'],'Copied source Git-blob mismatch: '+pin['local'])
    if skip:return {'frozen_equation_hashes_checked':len(EXPECTED),'copied_source_byte_pins_checked':len(pins),'release_manifest':'explicitly skipped'}
    lines=(ROOT/'SHA256SUMS').read_text().splitlines()
    seen=set()
    for line in lines:
        digest,path=line.split('  ',1)
        file=ROOT/path
        need(not Path(path).is_absolute() and '..' not in Path(path).parts,'Unsafe manifest path')
        need(path not in seen,'Duplicate manifest path');seen.add(path)
        need(file.is_file() and hashlib.sha256(file.read_bytes()).hexdigest()==digest,'Manifest mismatch: '+path)
    return {'frozen_equation_hashes_checked':len(EXPECTED),'copied_source_byte_pins_checked':len(pins),'manifest_files_checked':len(seen)}

def evaluator_controls():
    spec=importlib.util.spec_from_file_location('literal_evaluator',ROOT/'evaluate.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    eq=read('equations/principal/equation.json');n=len(eq['variables'])
    valid=mod.evaluate(eq,[0]*n)
    need(valid['polynomial_value']>0 and not valid['is_zero'],'Unexpected zero control')
    invalid=[None,{},[0]*(n-1),[0]*(n+1),[False]+[0]*(n-1),[0.0]+[0]*(n-1),['0']+[0]*(n-1)]
    for point in invalid:
        try:mod.evaluate(eq,point)
        except ValueError:pass
        else:raise ValueError('Invalid coordinate input accepted')
    return {'zero_tuple_value':valid['polynomial_value'],'invalid_inputs_rejected':len(invalid),
            'scope':'Evaluator control only; no search for roots.'}

def verify(args):
    receipt={'status':'PASS','python_optimized':bool(sys.flags.optimize),'integrity':integrity(args.skip_manifest)}
    with tempfile.TemporaryDirectory(prefix='conzfc-replay-') as td:
        temp=Path(td)
        depth=run('code/check_constructor_depth.py')
        need(depth==read('verification/CONSTRUCTOR_DEPTH_CERTIFICATE.json'),'Constructor AST certificate mismatch')
        receipt['constructor_depth']={'source_sha256':depth['source_sha256'],
            'outputs_compared':depth['source_outputs_compared'],'axiom_depths':depth['axiom_depths']}
        majorants=run('code/schema_audit.py')
        need(majorants==read('verification/SCHEMA_MAJORANTS.json'),'Local degree/majorant ledger mismatch')
        need(majorants['old']['local_majorant_exponent']<2**23,'Retained local bound insufficient')
        receipt['local_majorant_exponent']=majorants['old']['local_majorant_exponent']
        receipt['source_grafts']=[]
        receipt['source_rebuilds']=[]
        for profile,flags in [(221,['--quartic-index']),(220,['--explicit-index']),(219,[])]:
            dest=temp/f'anchor{profile}'
            run('code/build_anchor.py','--output',dest,*flags)
            for name in ['equation.json','certificate.json','expanded_polynomial.json','uncontracted.json','metrics.json']:
                need((dest/name).read_bytes()==(ROOT/f'source/anchor{profile}'/name).read_bytes(),
                     f'Source rebuild differs: {profile}/{name}')
            receipt['source_rebuilds'].append({'profile':profile,'five_files_byte_identical':True})
            receipt['source_grafts'].append(run('code/audit_anchor221.py','--profile',profile,
                '--parent-equation',ROOT/'source/parent225/equation.json',
                '--target-dir',ROOT/f'source/anchor{profile}',
                '--receipt',temp/f'anchor{profile}_audit.json'))
        receipt['projections']=[]
        for source,radical,affine in [('anchor221','projection216','affine215'),
                                      ('anchor220','projection215_explicit','affine214'),
                                      ('anchor219','projection214_affine','affine213')]:
            receipt['projections'].append(run('code/audit_projection.py',ROOT/f'source/{source}/equation.json',
                                              ROOT/f'stages/{radical}'))
            receipt['projections'].append(run('code/audit_projection.py',ROOT/f'stages/{radical}/equation.json',
                                              ROOT/f'stages/{affine}','--affine-mode'))
        receipt['optimizations']=run('code/audit_optimizations.py',ROOT/'OPTIMIZATION_CHAIN.json',
                                      '--receipt',temp/'optimization_audit.json')
        for profile in read('OPTIMIZATION_CHAIN.json')['profiles']:
            n=profile['name'][1:]
            final='equations/principal' if n=='215' else f'equations/companions/p{n}'
            last=Path(profile['stages'][-1]['equation'])
            for name in ['equation.json','expanded_polynomial.json']:
                need((ROOT/final/name).read_bytes()==(ROOT/last.parent/name).read_bytes(),
                     f'Final deliverable differs from replay endpoint: {n}/{name}')
        receipt['printed_equation']=run('code/check_printed_equation.py',ROOT)
        receipt['evaluator']=evaluator_controls()
        receipt['coefficient_rebuild']=run('code/rebuild.py','--output-dir',temp/'rebuilt')
        receipt=sanitize(receipt,temp)
    receipt['scope']=(
        'Exact source deltas, AST bounds, polynomial transformations and inverses, '
        'coefficient collection, literal TeX parsing, and reproducible coefficient rebuild. '
        'Not an end-to-end proof-assistant verification or a proof of Con(ZFC).')
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--skip-manifest',action='store_true',help='For pre-release authoring before SHA256SUMS exists.')
    verify(parser.parse_args())
