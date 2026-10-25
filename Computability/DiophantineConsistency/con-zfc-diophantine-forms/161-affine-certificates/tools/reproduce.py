#!/usr/bin/env python3
"""Rebuild and independently verify all delivered polynomial profiles.

Only Python's standard library is needed. Parent code is never imported.
Temporary reconstruction is removed on success or failure. No network access.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
TOOLS=ROOT/'tools'
ARCHIVE=ROOT/'provenance/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip'
EXPECTED='38dfec4f7db8ba4af921fe101714da6a569a3afce1d916325eb550160372c913'

def run(tool,*arguments):
    flags=['-B']+(['-O'] if sys.flags.optimize else [])
    p=subprocess.run([sys.executable,*flags,str(TOOLS/tool),*map(str,arguments)],
                     cwd=ROOT,text=True,capture_output=True)
    if p.returncode:
        raise RuntimeError(tool+' failed\n'+p.stdout+'\n'+p.stderr)
    return p.stdout

def same(a,b):
    if json.loads(a.read_bytes())!=json.loads(b.read_bytes()):
        raise ValueError('Rebuilt artifact differs: '+str(b.relative_to(ROOT)))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    if hashlib.sha256(ARCHIVE.read_bytes()).hexdigest()!=EXPECTED:
        raise ValueError('Inherited archive hash differs')
    report={'source_archive_sha256':EXPECTED,'optimized_python':bool(sys.flags.optimize),'stages':{}}
    with tempfile.TemporaryDirectory(prefix='conzfc-rebuild-') as tmp:
        tmp=Path(tmp)
        run('build_affine.py','--archive',ARCHIVE,'--output',tmp/'affine')
        for profile in ['principal','companion']:
            for name in ['equation.json','expanded_polynomial.json','certificate.json','metrics.json']:
                same(tmp/'affine'/profile/name,ROOT/'stages/affine'/profile/name)
        report['stages']['affine_lineage']=json.loads(run('verify_affine.py','--archive',ARCHIVE,'--equations',tmp/'affine'))
        run('build_horizon_free.py','--archive',ARCHIVE,'--output',tmp/'horizon')
        for name in ['raw_source.json','projection_certificate.json','source_changes.json']:
            same(tmp/'horizon'/name,ROOT/'stages/horizon'/name)
        for profile in ['principal','companion']:
            for name in ['equation.json','expanded_polynomial.json','affine_certificate.json','final_certificate.json','metrics.json']:
                same(tmp/'horizon'/profile/name,ROOT/'stages/horizon'/profile/name)
        report['stages']['horizon_lineage']=json.loads(run('verify_horizon_lineage.py',ARCHIVE,tmp/'horizon'))
        for stage,profile,name in [('affine','principal','balanced239'),('affine','companion','fewer238'),
                                   ('horizon','principal','horizon238'),('horizon','companion','horizon237')]:
            expected=ROOT/'equations'/name
            cert=json.loads((expected/'projection_certificate.json').read_bytes())
            out=tmp/name
            run('build_projection.py',tmp/stage/profile/'equation.json',cert['pivot_row'],cert['deleted_variable'],out)
            for filename in ['equation.json','expanded_polynomial.json','METRICS.json','projection_certificate.json']:
                same(out/filename,expected/filename)
            report['stages'][name]=json.loads(run('verify_projection.py',out))
        report['stages']['literal_power_binding']=json.loads(run(
            'audit_horizon_binding.py','--archive',ARCHIVE,
            '--source-root',tmp/'horizon',
            '--principal-d-input',tmp/'horizon238/source_equation.json',
            '--companion-d-input',tmp/'horizon237/source_equation.json',
            '--output',tmp/'literal_binding.json'))
    report['printed_appendix']=json.loads(run('build_report.py','--check'))
    report['status']='PASS'
    report['scope']='Exact source lineage, all finite coefficients, zero-set maps and printed appendix; unbounded mathematical calibration is supplied in the proofs.'
    result=json.dumps(report,sort_keys=True,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(result)
    print(result,end='')

if __name__=='__main__':main()
