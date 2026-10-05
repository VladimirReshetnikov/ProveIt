#!/usr/bin/env python3
"""Deliberate corruption regressions. Successful detection is an expected failure."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import verify as V
from formal_engine import VerificationError, require, zero, integrate_endpoint, direct_ratio, ratio_from_log

ROOT=Path(__file__).resolve().parent

def main():
    print(f'Negative regression process: optimization={sys.flags.optimize}',flush=True)
    V.check_integrity(ROOT)
    formal,linear,endpoint=V.check_schema(ROOT)
    passed=[]
    def expect_failure(name,operation,fragment):
        try:
            operation()
        except VerificationError as error:
            require(fragment in str(error),f'{name}: unexpected failure reason: {error}')
            passed.append(name)
            print(f'PASS rejection: {name}: {error}',flush=True)
            return
        raise VerificationError(f'{name}: corruption was accepted')
    expect_failure('active explicit gate',lambda:require(False,'deliberate gate'),'deliberate gate')
    expect_failure('zero algebra coverage',lambda:V.check_algebra(0),'exactly n=1..30')
    expect_failure('boolean algebra coverage',lambda:V.check_algebra(True),'exactly n=1..30')
    expect_failure('reduced formal coverage',lambda:V.check_formal(formal,linear,endpoint,8),'exactly order 9')
    expect_failure('boolean formal coverage',lambda:V.check_formal(formal,linear,endpoint,True),'exactly order 9')
    for filename in ('verify.py','formal_engine.py','negative_tests.py'):
        tree=ast.parse((ROOT/filename).read_text())
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)),f'{filename}: optimized-away assertion acceptance gate')
    print('PASS code audit: no Python assert statements in any executable checker',flush=True)
    raw_formal=V.read_json(ROOT/'data/formal_9.json')
    raw_endpoint=V.read_json(ROOT/'data/endpoint_9.json')
    with tempfile.TemporaryDirectory(prefix='relaxed-tree-negative-') as temporary:
        base=Path(temporary)
        def file_case(name,raw,mutate,loader,fragment):
            value=copy.deepcopy(raw)
            mutate(value)
            path=base/(name+'.json')
            path.write_text(json.dumps(value))
            expect_failure(name,lambda:loader(path),fragment)
        file_case('empty formal table',raw_formal,lambda obj:obj.clear(),V.load_formal,'exactly keys')
        file_case('missing compacted kind',raw_formal,lambda obj:obj.pop('C'),V.load_formal,'exactly keys')
        file_case('unexpected sequence kind',raw_formal,lambda obj:obj.update(X={}),V.load_formal,'exactly keys')
        file_case('empty profile array',raw_formal,lambda obj:obj['R'].update(f=[]),V.load_formal,'8 indexed entries')
        file_case('missing profile index',raw_formal,lambda obj:obj['R']['f'].pop(),V.load_formal,'8 indexed entries')
        file_case('extra profile index',raw_formal,lambda obj:obj['R']['f'].append(['0','0']),V.load_formal,'8 indexed entries')
        file_case('malformed profile pair',raw_formal,lambda obj:obj['R']['f'][1].pop(),V.load_formal,'2 indexed entries')
        file_case('empty sigma array',raw_formal,lambda obj:obj['R'].update(sigma=[]),V.load_formal,'10 indexed entries')
        file_case('missing sigma index',raw_formal,lambda obj:obj['R']['sigma'].pop(),V.load_formal,'10 indexed entries')
        file_case('numeric floating polynomial',raw_formal,lambda obj:obj['R']['sigma'].__setitem__(3,2.5),V.load_formal,'polynomial string')
        file_case('floating literal polynomial',raw_formal,lambda obj:obj['R']['sigma'].__setitem__(3,'2.5'),V.load_formal,'unsupported expression syntax')
        file_case('unknown polynomial symbol',raw_formal,lambda obj:obj['R']['sigma'].__setitem__(3,'z'),V.load_formal,'unsupported expression syntax')
        file_case('function expression rejected',raw_formal,lambda obj:obj['R']['sigma'].__setitem__(3,'sqrt(2)'),V.load_formal,'unsupported expression syntax')
        file_case('negative degree rejected',raw_formal,lambda obj:obj['R']['sigma'].__setitem__(3,'k**(-1)'),V.load_formal,'exponent must')
        file_case('zero denominator rejected',raw_formal,lambda obj:obj['R']['sigma'].__setitem__(3,'1/0'),V.load_formal,'nonzero rational constant')
        file_case('wrong leading profile',raw_formal,lambda obj:obj['R']['f'][0].__setitem__(0,'2'),V.load_formal,'f0 normalization')
        file_case('empty endpoint table',raw_endpoint,lambda obj:obj.clear(),V.load_endpoint,'exactly keys')
        for key,size in (('log_correction',6),('multiplicative',7),('ratio',10)):
            file_case('missing '+key+' index',raw_endpoint,lambda obj,key=key:obj['R'][key].pop(),V.load_endpoint,f'{size} indexed entries')
        duplicate=base/'duplicate.json'
        duplicate.write_text('{"R": {}, "R": {}, "C": {}}')
        expect_failure('duplicate JSON key',lambda:V.load_formal(duplicate),'duplicate JSON key')
        nan=base/'nonfinite.json';nan.write_text('{"R": NaN, "C": {}}')
        expect_failure('nonfinite JSON',lambda:V.load_formal(nan),'nonfinite JSON value')
        # Integrity regressions use a private copy; the accepted source package is untouched.
        sandbox=base/'package'
        shutil.copytree(ROOT,sandbox,ignore=shutil.ignore_patterns('__pycache__','logs'))
        original_manifest=V.read_json(sandbox/'manifest.json')
        path=sandbox/'data/formal_9.json'
        original=path.read_bytes()
        path.write_bytes(original+b'\n')
        expect_failure('unrecorded data edit',lambda:V.check_integrity(sandbox),'byte count mismatch')
        path.write_bytes(original.replace(b'8/3',b'7/3',1))
        expect_failure('same-length data edit',lambda:V.check_integrity(sandbox),'SHA-256 mismatch')
        path.write_bytes(original)
        for name,change,fragment in (
            ('missing manifest entry',lambda obj:obj['files'].pop('formal_engine.py'),'exactly keys'),
            ('extra manifest entry',lambda obj:obj['files'].update({'unexpected.py':{}}),'exactly keys'),
            ('invalid manifest hash',lambda obj:obj['files']['formal_engine.py'].update(sha256='xyz'),'SHA-256 syntax'),
            ('boolean manifest byte count',lambda obj:obj['files']['formal_engine.py'].update(bytes=True),'byte count'),
        ):
            manifest=copy.deepcopy(original_manifest);change(manifest)
            (sandbox/'manifest.json').write_text(json.dumps(manifest))
            expect_failure(name,lambda:V.check_integrity(sandbox),fragment)
        (sandbox/'manifest.json').write_text(json.dumps(original_manifest))
        unexpected=sandbox/'data/extra.json';unexpected.write_text('{}')
        expect_failure('extra data file',lambda:V.check_schema(sandbox),'inventory mismatch')
        unexpected.unlink()
        extra_source=sandbox/'extra.py';extra_source.write_text('# unexpected source\n')
        expect_failure('extra executable source',lambda:V.check_integrity(sandbox),'source inventory mismatch')
        extra_source.unlink()
        # Re-signing this intentionally broken local copy bypasses only the hash gate;
        # it demonstrates that mathematical acceptance gates also reject corruption.
        script=sandbox/'verify.py'
        old=script.read_text()
        needle='F((n-j+1)**2,(n+j)*(n+j-1))*old[j-1]'
        require(old.count(needle)==1,'negative algebra mutation target not unique')
        script.write_text(old.replace(needle,'F((n-j+1)**2+1,(n+j)*(n+j-1))*old[j-1]'))
        content=script.read_bytes()
        manifest=copy.deepcopy(original_manifest)
        manifest['files']['verify.py']={'bytes':len(content),'sha256':hashlib.sha256(content).hexdigest()}
        (sandbox/'manifest.json').write_text(json.dumps(manifest))
        command=[sys.executable]+(['-O'] if sys.flags.optimize else [])+[str(script),'--mode','algebra']
        result=subprocess.run(command,capture_output=True,text=True,timeout=90)
        require(result.returncode!=0 and 'two-step actual vector' in result.stderr,'deliberate algebra error not rejected for intended reason')
        passed.append('corrupted two-step coefficient')
        print('PASS rejection: corrupted two-step coefficient: '+result.stderr.strip(),flush=True)
        # All CLI errors must exit as argument errors, before a PASS is printed.
        for flag,value in (('--max-n','0'),('--max-n','-1'),('--max-n','29'),('--max-n','31'),('--max-n','30.0'),('--max-n','true'),('--formal-order','0'),('--formal-order','8'),('--formal-order','10'),('--formal-order','9.0'),('--formal-order','false'),('--mode','unknown'),('--not-a-real-option','value')):
            command=[sys.executable]+(['-O'] if sys.flags.optimize else [])+[str(ROOT/'verify.py'),flag,value]
            result=subprocess.run(command,capture_output=True,text=True,timeout=30)
            require(result.returncode==2 and 'PASS' not in result.stdout,f'CLI {flag}={value} did not fail closed')
            passed.append('CLI '+flag+'='+value)
            print('PASS rejection: CLI '+flag+'='+value+' (exit 2, no PASS output)',flush=True)
        # A nontrivial profile edit respects schema and boundary, but fails recurrence.
        corrupted=copy.deepcopy(formal)
        corrupted['R'][0][2][0]+=V.x**2
        expect_failure('boundary-preserving formal coefficient edit',lambda:V.check_formal(corrupted,linear,endpoint,9),'recurrence residual')
        # Endpoint coefficient families are checked against freshly computed certificates.
        E,logs,multiplicative=integrate_endpoint(*formal['R'])
        ratio=direct_ratio(E,formal['R'][1])
        from_log=ratio_from_log(logs,'R')
        require(all(zero(u-v) for u,v in zip(ratio,from_log)),'negative suite baseline endpoint mismatch')
        for family,actual,index in (('log_correction',logs,0),('multiplicative',multiplicative,6),('ratio',ratio,9)):
            corrupted=copy.deepcopy(endpoint['R']);corrupted[family][index]+=1
            expect_failure('corrupted endpoint '+family,lambda corrupted=corrupted:V.compare_endpoint_certificates('R',logs,multiplicative,ratio,from_log,corrupted),'endpoint '+family)
    require(len(passed)==53,f'negative regression coverage mismatch: {len(passed)} instead of 53')
    print(f'COMPLETE negative regressions: {len(passed)} expected rejections, optimization={sys.flags.optimize}; no archived diagnostics were recomputed',flush=True)
    return 0

if __name__=='__main__':
    try:
        sys.exit(main())
    except VerificationError as error:
        print(f'FAIL negative suite: {error}',file=sys.stderr,flush=True)
        sys.exit(1)
