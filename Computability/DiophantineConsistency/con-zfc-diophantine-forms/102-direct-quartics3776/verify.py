#!/usr/bin/env python3
"""Offline exact verification of the complete released quartic package.

All executable checks run in a fresh temporary copy. The delivered data are
never rewritten. Use --regenerate to rerun the slower elimination searches.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent


def need(test,message):
    if not test:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path)
    parser.add_argument('--regenerate',action='store_true')
    args=parser.parse_args()
    manifest=HERE/'SHA256SUMS'
    authenticated=0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected,name=line.split('  ',1)
            path=HERE/name
            need(path.is_file() and digest(path)==expected,'release identity mismatch: '+name)
            authenticated+=1
    for record in json.loads((HERE/'source_calibration/SOURCE_URLS.json').read_text())['files']:
        path=HERE/'source_calibration'/record['file']
        need(digest(path)==record['sha256'],'calibration source identity: '+record['file'])
        need(path.stat().st_size==record['bytes'],'calibration byte count: '+record['file'])
    py=[sys.executable]+(['-O'] if sys.flags.optimize else [])
    stages=[]
    with tempfile.TemporaryDirectory(prefix='conzfc-release-') as scratch:
        root=Path(scratch)/'package'
        shutil.copytree(HERE,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.log','*.aux','*.out','*.toc'))

        def run(label,arguments):
            result=subprocess.run(py+[str(root/arguments[0])]+[str(x) for x in arguments[1:]],
                                  cwd=root,text=True,capture_output=True)
            if result.returncode:
                raise RuntimeError(label+' failed:\n'+result.stdout[-6000:]+result.stderr[-6000:])
            stages.append({'name':label,'status':'PASS'})
            print('PASS '+label,flush=True)
            return result.stdout

        def same_output(relative,builder_arguments,filenames):
            before={name:digest(root/relative/name) for name in filenames}
            run('regenerate '+relative,builder_arguments)
            need(before=={name:digest(root/relative/name) for name in filenames},
                 'regeneration changed literal files: '+relative)

        run('complete frozen natural-source regeneration and arithmetic audits',
            ['signed_quotients/verify_sources.py'])
        signed_files=['equation.json','expanded_polynomial.json','transformation_certificate.json']
        same_output('signed_quotients/candidate',['signed_quotients/build.py'],signed_files)
        same_output('signed_quotients/retained_candidate',['signed_quotients/build.py','--retained'],signed_files)
        run('independent signed quotient proof, affine source',['signed_quotients/check.py'])
        run('independent signed quotient proof, retained source',['signed_quotients/check.py','--retained'])

        guard_files=['equation.json','expanded_polynomial.json','guard_certificate.json']
        same_output('guard_minimization/candidate',['guard_minimization/build.py'],guard_files)
        same_output('guard_minimization/retained_candidate',
                    ['guard_minimization/build.py','--source',root/'signed_quotients/retained_candidate/equation.json',
                     '--optimization',root/'guard_minimization/retained_preliminary.json',
                     '--output',root/'guard_minimization/retained_candidate'],guard_files)
        run('independent affine-core sign and bound certificates',['guard_minimization/check.py'])
        run('independent retained-core sign and bound certificates',
            ['guard_minimization/check.py','--source',root/'signed_quotients/retained_candidate/equation.json',
             '--candidate',root/'guard_minimization/retained_candidate'])

        endpoints=[('main','guard_minimization/retained_candidate',2,2),
                   ('fewer_variables','guard_minimization/candidate',18,24)]
        for name,parent,affine_cap,quadratic_cap in endpoints:
            directory=root/'equations'/name
            source=root/parent/'equation.json'
            if args.regenerate:
                same_output('equations/'+name,
                            ['elimination/build.py',source,directory,'--affine-cap',str(affine_cap),
                             '--quadratic-cap',str(quadratic_cap)],
                            ['equation.json','expanded_polynomial.json','elimination_certificate.json'])
            run('independent complete elimination and quartic expansion: '+name,
                ['elimination/check.py',source,directory,'--receipt',directory/'CURRENT_CHECK.json'])
        run('adversarial sign-certificate controls in both Python modes',
            ['guard_minimization/corruption_controls.py'])

    result={'status':'PASS','python_optimization':sys.flags.optimize,
            'release_files_authenticated':authenticated,'full_elimination_search_regenerated':args.regenerate,
            'source_calibration_files_authenticated':13,'stages':stages,
            'scope':'Exact finite algebra, source identities, explicit proof certificates and whole polynomial coefficients. No consistency decision and no new Lean build.'}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
