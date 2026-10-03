#!/usr/bin/env python3
"""Reproduce and validate the release without modifying its source files."""
from pathlib import Path
import argparse, gzip, hashlib, json, shutil, subprocess, sys, tempfile

ROOT=Path(__file__).resolve().parents[1]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--regenerate-source',action='store_true')
    args=parser.parse_args()
    workroot=ROOT/'.replay'; workroot.mkdir(exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='run-',dir=workroot))
    code=work/'replay'; shutil.copytree(ROOT/'replay',code,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    out=work/'results';out.mkdir()
    stages=[]
    def run(name,command):
        print(f'Checking {name}',flush=True)
        p=subprocess.run(command,cwd=work,text=True,capture_output=True)
        (out/(name+'.stdout')).write_text(p.stdout)
        (out/(name+'.stderr')).write_text(p.stderr)
        if p.returncode:
            print(p.stdout[-6000:]);print(p.stderr[-6000:],file=sys.stderr)
            raise RuntimeError(f'{name} failed with exit {p.returncode}')
        stages.append(name)
        return p.stdout
    def same_json(new,old,ignore=()):
        a=json.loads(Path(new).read_text());b=json.loads(Path(old).read_text())
        for key in ignore:a.pop(key,None);b.pop(key,None)
        if a!=b:raise AssertionError(f'Receipt mismatch: {new.name} and {old.name}')
    py=sys.executable
    text=run('poly-exactness',[py,str(code/'core/test_poly_exactness.py')])
    (out/'poly-exactness.json').write_text(text)
    same_json(out/'poly-exactness.json',ROOT/'receipts/poly-exactness.json')
    run('core-checks',[py,str(code/'core/run_checks.py')])
    same_json(code/'core/check_results.json',ROOT/'receipts/core-checks.json')
    for p in (ROOT/'replay/core/fixtures').glob('*.json'):
        if p.read_bytes()!=(code/'core/fixtures'/p.name).read_bytes():raise AssertionError('Fixture mismatch: '+p.name)
    for name,script,receipt in [
        ('independent-dynamics','independent_dynamics.py','independent-dynamics.json'),
        ('legacy-factorized','independent_polynomial_audit.py','legacy-factorized.json'),
        ('independent-rows','independent_row_polynomial_audit.py','independent-rows.json')]:
        text=run(name,[py,str(code/'independent'/script)])
        f=out/(name+'.json');f.write_text(text);same_json(f,ROOT/'receipts'/receipt)
    text=run('coefficient-crosscheck',[py,str(code/'independent/crosscheck_row_producer.py'),str(code/'core/sparse_mass.py')])
    f=out/'coefficient-crosscheck.json';f.write_text(text)
    same_json(f,ROOT/'receipts/coefficient-crosscheck.json',ignore=('producer_sha256',))
    actual_hash=hashlib.sha256((code/'core/sparse_mass.py').read_bytes()).hexdigest()
    assert json.loads(text)['producer_sha256']==actual_hash
    run('morita-source',[py,str(code/'morita/audit.py')])
    same_json(code/'morita/audit-results.json',ROOT/'receipts/morita-source.json')
    for name in ('doubling-complete.csv','false-signal-complete.csv'):
        if (code/'morita'/name).read_bytes()!=(ROOT/'tables'/name).read_bytes():raise AssertionError('Table mismatch: '+name)
    text=run('two-mass-arithmetic',[py,str(code/'two-mass/audit.py')])
    f=out/'two-mass-arithmetic.json';f.write_text(text);same_json(f,ROOT/'receipts/two-mass-arithmetic.json')
    run('two-mass-regression',[py,str(code/'two-mass/regression.py')])
    for name,script,receipt in [
        ('semilinearity-components','check.py','semilinearity-components.json'),
        ('semilinearity-independent','audit.py','semilinearity-independent.json')]:
        text=run(name,[py,str(code/'semilinearity'/script)])
        f=out/(name+'.json');f.write_text(text)
        same_json(f,ROOT/'receipts'/receipt,ignore=('sha256',))
    for p in sorted((code/'core/fixtures').glob('*')):
        if p.suffix in ('.json','.gz'):
            run('bound-'+p.name.replace('.','-'),[py,str(code/'core/sparse_mass.py'),str(p)])
    if args.regenerate_source:
        for n in (0,2):
            run('regenerate-morita-'+str(n),[py,str(code/'core/run_morita_fixture.py'),'--input',str(n)])
            same_json(code/'core'/f'morita_fixture_n{n}_results.json',ROOT/'receipts'/f'morita-n{n}.json')
            T=7 if n==0 else 41
            name=f'morita_doubling_n{n}_pulse_T{T}.json.gz'
            if gzip.decompress((code/'core/fixtures'/name).read_bytes())!=gzip.decompress((ROOT/'replay/core/fixtures'/name).read_bytes()):
                raise AssertionError('Decompressed coefficient fixture differs: '+name)
    report={'status':'PASS','stages':stages,'source_regenerated':args.regenerate_source,
            'packaged_producer_sha256':actual_hash,'python':sys.version.split()[0],
            'scope':'Exact replay and stable receipt/table/fixture comparison. Finite tests supplement the report proofs.'}
    (out/'release-verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2));print('Fresh output directory:',work)

if __name__=='__main__':main()
