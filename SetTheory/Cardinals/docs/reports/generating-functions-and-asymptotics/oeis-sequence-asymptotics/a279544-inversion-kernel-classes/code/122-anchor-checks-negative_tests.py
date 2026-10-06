#!/usr/bin/env python3
"""Mutation tests in disposable external copies; each case checks its diagnostic.
The complete matrix is run in normal and optimized Python by this script itself.
"""
import sys
sys.dont_write_bytecode=True
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
from exact_model import require

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent


def hash_files(root):
    return {p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file()}


def seal(checks):
    inv=json.loads((checks/'inventory.json').read_text())
    inv['files']={name:hashlib.sha256((checks/name).read_bytes()).hexdigest() for name in inv['files']}
    (checks/'inventory.json').write_text(json.dumps(inv,indent=2,sort_keys=True)+'\n')


def half(value):
    q=Fraction(value)/2
    return str(q.numerator)+'/'+str(q.denominator)


def mutations():
    return [
      ('unknown-key','schema','schema: top-level keys',lambda d:d.update(unexpected=1)),
      ('boolean-version','schema','schema: version must be integer, not boolean',lambda d:d.update(schema=True)),
      ('unreduced-rational','schema','schema: rho is not a canonical rational',lambda d:d['analytic']['parameters'].update(rho='8/54')),
      ('zero-denominator','schema','schema: rho is not a canonical rational',lambda d:d['analytic']['parameters'].update(rho='4/0')),
      ('negative-zero','schema','schema: source T correction is not a canonical rational',lambda d:d['model'].update(source_T_correction='-0/1')),
      ('wrong-range','schema','schema: tree_max_n below minimum',lambda d:d['model'].update(tree_max_n=149)),
      ('noncanonical-integer','schema','schema: generated term is not canonical integer string',lambda d:d['model']['generated_terms'].__setitem__(0,'01')),
      ('reversed-interval','schema','schema: reversed claimed interval C',lambda d:d['analytic']['claimed_intervals']['C'].reverse()),
      ('critical-rho','preflight','domain: wrong critical rho',lambda d:d['analytic']['parameters'].update(rho='1/7')),
      ('contraction-domain','preflight','domain: complex contraction bound fails',lambda d:d['analytic']['parameters'].update(Z='1/5')),
      ('tail-too-small','preflight','tail: claimed E is smaller than proved remainder',lambda d:d['analytic'].update(tail_E=half(d['analytic']['tail_E']))),
      ('derivative-tail','preflight','tail: derivative Cauchy remainder too small',lambda d:d['analytic'].update(derivative_tail=half(d['analytic']['derivative_tail']))),
      ('coefficient-tail','preflight','tail: coefficient Cauchy remainder too small',lambda d:d['analytic']['coefficient_tails'].update({'5':half(d['analytic']['coefficient_tails']['5'])})),
      ('global-invariance','preflight','global: lower-orbit disk is not invariant',lambda d:d['analytic'].update(denominator_disk_B='7/6')),
      ('global-floor','preflight','global: claimed denominator floor too large',lambda d:d['analytic'].update(denominator_modulus_floor='1/1')),
      ('root-fifth-coefficient','preflight','root: Puiseux equation residual through t^6',lambda d:d['analytic']['root_jet'][5].__setitem__(1,'-1/4')),
      ('published-prefix','finite','prefix: published 26-term sequence mismatch',lambda d:d['model']['published_prefix'].__setitem__(25,d['model']['published_prefix'][25]+1)),
      ('generated-a150','finite','sequence: generated n=0..150 mismatch',lambda d:d['model']['generated_terms'].__setitem__(150,str(int(d['model']['generated_terms'][150])+1))),
      ('all-zero-correction','finite','functional: source T all-zero correction residual',lambda d:d['model'].update(source_T_correction='0/1')),
      ('orbit-next-coefficient','finite','orbit: next coefficient discrepancy mismatch',lambda d:d['model']['orbit_next_differences'].__setitem__(0,'2/1')),
      ('amplitude-interval','analytic','interval: C outside claimed interval',lambda d:d['analytic']['claimed_intervals'].update(C=['1/1','2/1'])),
      ('correction-interval','analytic','interval: d2 outside claimed interval',lambda d:d['analytic']['claimed_intervals'].update(d2=['4915/1','4916/1'])),
    ]


def main():
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args(); output=args.output.resolve()
    require(not output.is_relative_to(PACKAGE),'output: path must be outside package')
    before=hash_files(HERE); results=[]
    with tempfile.TemporaryDirectory(prefix='report122-negative-') as tmp:
        root=Path(tmp)
        for optimized in (False,True):
            mode='optimized' if optimized else 'normal'
            cases=mutations()+[
                ('duplicate-key','schema','schema: duplicate JSON key schema',None),
                ('unsealed-edit','schema','inventory: digest mismatch for certificate.json',None),
                ('extra-file','schema','inventory: closed file inventory mismatch',None),
                ('extra-directory','schema','inventory: unexpected directory',None),
                ('symlink','schema','inventory: symlink is forbidden',None),
                ('missing-file','schema','inventory: closed file inventory mismatch',None),
                ('internal-output','schema','output: path must be outside package',None)]
            for name,stage,diagnostic,mutation in cases:
                case=root/(mode+'-'+name); checks=case/'package'/'checks'
                shutil.copytree(HERE,checks)
                data=json.loads((checks/'certificate.json').read_text())
                if mutation:
                    mutation(data)
                    (checks/'certificate.json').write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
                    seal(checks)
                elif name=='duplicate-key':
                    txt=(checks/'certificate.json').read_text()
                    (checks/'certificate.json').write_text('{"schema":1,'+txt[1:]); seal(checks)
                elif name=='unsealed-edit': (checks/'certificate.json').write_text('{}\n')
                elif name=='extra-file': (checks/'extra.txt').write_text('unlisted\n')
                elif name=='extra-directory': (checks/'extra').mkdir()
                elif name=='symlink': (checks/'unexpected-link').symlink_to(checks/'README.md')
                elif name=='missing-file': (checks/'README.md').unlink()
                destination=checks/'forbidden.json' if name=='internal-output' else case/'result.json'
                cmd=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(checks/'verify.py'),'--stage',stage,'--output',str(destination)]
                run=subprocess.run(cmd,text=True,capture_output=True)
                require(run.returncode==2 and diagnostic in run.stderr,
                        'negative test '+mode+'/'+name+' failed expected diagnostic '+diagnostic+'; got '+str(run.returncode)+' '+run.stderr)
                require(not destination.exists(),'negative test wrote success output: '+name)
                results.append({'case':name,'mode':mode,'exit_code':run.returncode,'diagnostic':diagnostic})
                print('PASS rejection '+mode+'/'+name,flush=True)
    require(hash_files(HERE)==before,'negative tests modified delivered inventory')
    summary={'schema':1,'status':'PASS','cases_per_mode':len(results)//2,'executions':len(results),
             'source_inventory_preserved':True,'tests':results}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print('PASS report122 negative tests: '+str(len(results))+' rejected cases; '+str(output))

if __name__=='__main__':
    try: main()
    except ValueError as error:
        print('FAIL '+str(error),file=sys.stderr);sys.exit(2)
