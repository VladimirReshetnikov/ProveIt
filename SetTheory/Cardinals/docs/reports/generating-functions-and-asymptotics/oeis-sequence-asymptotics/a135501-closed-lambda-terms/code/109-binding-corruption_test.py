#!/usr/bin/env python3
"""Mutation tests in disposable copies, normal and optimized Python.
The mathematical runs bypass the manifest intentionally, so a hash mismatch
cannot disguise an inactive mathematical guard. All originals stay untouched.
"""
from pathlib import Path
from hashlib import sha256
import json
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:
        raise RuntimeError(message)

def replace_once(path,old,new):
    source=path.read_text()
    require(source.count(old)==1,f'mutation target ambiguous: {old!r}')
    path.write_text(source.replace(old,new,1))

def mutate_logic(root,old,new):
    replace_once(root/'check.py',old,new)

def mutate_fixture(root,kind):
    path=root/'data/A220894_computed.txt'
    lines=path.read_text().splitlines()
    if kind=='missing':
        path.unlink()
    elif kind=='extra':
        (root/'data/UNEXPECTED.txt').write_text('unexpected\n')
    elif kind=='truncated':
        path.write_text('\n'.join(lines[:-1])+'\n')
    elif kind=='malformed':
        lines[10]='10 not-an-integer'
        path.write_text('\n'.join(lines)+'\n')
    elif kind=='tail':
        lines[-1]='200 0'
        path.write_text('\n'.join(lines)+'\n')
    elif kind=='moment':
        path=root/'data/A135501_unary_moment.txt'
        lines=path.read_text().splitlines(); lines[100]='100 0'
        path.write_text('\n'.join(lines)+'\n')
    elif kind=='summary':
        path=root/'data/check_results.json'
        data=json.loads(path.read_text()); data['total_mathematical_checks']+=1
        path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    else:
        raise RuntimeError('unknown fixture mutant')

def main():
    for optimized in (False,True):
        command=[sys.executable]+(['-O'] if optimized else [])+['integrity.py']
        cp=subprocess.run(command,cwd=ROOT,text=True,capture_output=True)
        require(cp.returncode==0,'pristine integrity preflight failed: '+cp.stderr)
    manifest=json.loads((ROOT/'manifest.json').read_text())
    names=sorted(manifest['files'])+['manifest.json']
    original_hashes={name:sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    cases=[]
    logic=[
        ('zero-cost base','if s == 0:','if s == 1:'),
        ('admissibility parity','if (n-u-s) % (s+1) == 0:','if (n-u-s) % (s+1) != 0:'),
        ('Catalan lower bound','root = comb(2*b,b)//(b+1)*u**(b+1)','root = comb(2*b,b)//(b+1)*u**(b+2)'),
        ('uniform upper bound','2*u*12**u*(4*u)**b','0*u*12**u*(4*u)**b'),
        ('height statistic','counts[max(depths)] += prod(depths)','counts[min(depths)] += prod(depths)'),
        ('height construction','counts[h]>=cat*(h-1)**(b+1)','counts[h]>=cat*(h+1)**(b+1)'),
        ('deficit product','bound=Fraction(u**(2*u-1),factorial(u)**2)','bound=Fraction(u**(2*u-1),2*factorial(u)**2)'),
        ('shape recurrence','weighted[j]*weighted[u-j]/2','weighted[j]*weighted[u-j]/3'),
        ('radical denominator','comb(2*h,h)*m**h*inner','comb(2*h,h)*(m+1)**h*inner'),
    ]
    for label,old,new in logic:
        cases.append((f'logic: {label}','check.py',lambda root,o=old,n=new: mutate_logic(root,o,n)))
    for kind in ('missing','extra','truncated','malformed','tail','moment','summary'):
        cases.append((f'fixture: {kind}','check.py',lambda root,k=kind:mutate_fixture(root,k)))
    def damage(root,name):
        path=root/name; path.write_bytes(path.read_bytes()+b'\nCORRUPTED\n')
    for name in ('report109.tex','report109.pdf','check.py','data/A220894_computed.txt'):
        cases.append((f'integrity: {name}','integrity.py',lambda root,n=name:damage(root,n)))
    cases.append(('integrity: extra file','integrity.py',lambda root:(root/'unexpected.txt').write_text('extra\n')))
    cases.append(('integrity: missing file','integrity.py',lambda root:(root/'report109.pdf').unlink()))
    def manifest_mutant(root,kind):
        path=root/'manifest.json'
        data=json.loads(path.read_text())
        if kind=='duplicate key':
            path.write_text(path.read_text().replace('{','{\"schema\": 1,',1))
        elif kind=='boolean schema':
            data['schema']=True; path.write_text(json.dumps(data))
        elif kind=='boolean size':
            data['files']['report109.tex']['size_bytes']=True; path.write_text(json.dumps(data))
        elif kind=='nested build':
            path=root/'data/build/unexpected.txt'; path.parent.mkdir(); path.write_text('unexpected')
    for kind in ('duplicate key','boolean schema','boolean size','nested build'):
        cases.append((f'integrity: {kind}','integrity.py',lambda root,k=kind:manifest_mutant(root,k)))
    expected_diagnostics={
        'logic: zero-cost base':'published prefix', 'logic: admissibility parity':'total bounds',
        'logic: Catalan lower bound':'total bounds', 'logic: uniform upper bound':'rational majorant',
        'logic: height statistic':'height upper', 'logic: height construction':'height lower',
        'logic: deficit product':'deficit majorant', 'logic: shape recurrence':'shape recurrence',
        'logic: radical denominator':'direct/radical',
        'integrity: report109.tex':'integrity mismatch: report109.tex',
        'integrity: report109.pdf':'integrity mismatch: report109.pdf',
        'integrity: check.py':'integrity mismatch: check.py',
        'integrity: data/A220894_computed.txt':'integrity mismatch: data/A220894_computed.txt',
        'integrity: extra file':'inventory mismatch', 'integrity: missing file':'inventory mismatch',
        'integrity: duplicate key':'duplicate JSON key', 'integrity: boolean schema':'invalid manifest schema',
        'integrity: boolean size':'invalid size', 'integrity: nested build':'inventory mismatch',
    }
    results=[]
    with tempfile.TemporaryDirectory(prefix='report109-corruption-') as tmp:
        temp=Path(tmp)
        pristine=temp/'pristine'; pristine.mkdir()
        for name in names:
            dest=pristine/name; dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/name,dest)
            require(sha256(dest.read_bytes()).hexdigest()==original_hashes[name],
                    f'source changed during pristine copy: {name}')
        for index,(label,entry,mutation) in enumerate(cases):
            root=temp/str(index)
            shutil.copytree(pristine,root)
            mutation(root)
            for optimized in (False,True):
                command=[sys.executable]+(['-O'] if optimized else [])+[entry]
                cp=subprocess.run(command,cwd=root,text=True,capture_output=True)
                require(cp.returncode!=0,f'CORRUPTION ESCAPED: {label}, optimized={optimized}')
                # Missing input legitimately fails on open; all other test failures must reach guards.
                if 'missing' not in label:
                    require('RuntimeError:' in cp.stderr,f'not an explicit-guard failure: {label}: {cp.stderr}')
                if label in expected_diagnostics:
                    require('RuntimeError: '+expected_diagnostics[label] in cp.stderr,
                            f'wrong mathematical diagnostic: {label}: {cp.stderr}')
                require('SyntaxError:' not in cp.stderr,f'invalid mutation source: {label}')
                results.append({'case':label,'optimized':optimized,'rejected':True})
    for name,digest in original_hashes.items():
        require(sha256((ROOT/name).read_bytes()).hexdigest()==digest,f'original changed during campaign: {name}')
    print(json.dumps({'status':'PASS','mutation_cases':len(cases),'normal_and_optimized_rejections':len(results),
                      'originals_unchanged':True,'results':results},indent=2,sort_keys=True))

if __name__=='__main__':
    main()
