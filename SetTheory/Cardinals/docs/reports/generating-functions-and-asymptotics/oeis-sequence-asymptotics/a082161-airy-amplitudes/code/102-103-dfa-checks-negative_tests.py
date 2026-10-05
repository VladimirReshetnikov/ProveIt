#!/usr/bin/env python3
"""Deliberately invalid inputs must fail under both ordinary and optimized Python.

Semantic corruptions are made in independent in-memory copies after a valid
baseline has passed. This exercises the mathematics beyond the input hash gate.
No immutable release input or dependency is changed.
"""
import ast
from copy import deepcopy
from pathlib import Path
import platform
import shutil
import sys
import tempfile
import sympy as S
import verify as v
from formal_engine import VerificationError, require


def rejection(label,call):
    try:
        call()
    except VerificationError as error:
        print(f'REJECT {label}: {error}',flush=True)
        return
    raise VerificationError(f'negative test incorrectly accepted: {label}')


def main():
    print(f'Negative tests: Python {platform.python_version()}, SymPy {S.__version__}, optimize={sys.flags.optimize}',flush=True)
    data=v.load_all()
    v.check_dependencies(data['dependencies.json'])
    # Positive baseline prevents a permanently-failing checker from passing tests.
    d,e=v.check_triangle(data['exact.json'])
    v.check_elimination(data['exact.json'],e)
    v.check_gauge(data['exact.json'])
    v.check_formal(data['formal_7.json'],data['exact.json'],regenerate=False)
    v.check_endpoint(data['endpoint_7.json'],data['formal_7.json'])
    v.check_inverse(data['inverse.json'],data['endpoint_7.json'])
    cases=0
    def change(label,file,route,value,check):
        nonlocal cases
        copy=deepcopy(data[file]); where=copy
        for step in route[:-1]: where=where[step]
        where[route[-1]]=value
        rejection(label,lambda:check(copy))
        cases+=1
    exact=lambda changed:v.check_triangle(changed)
    memory=lambda changed:v.check_elimination(changed)
    formal=lambda changed:v.check_formal(changed,data['exact.json'],regenerate=False)
    endpoint=lambda changed:v.check_endpoint(changed,data['formal_7.json'])
    inverse=lambda changed:v.check_inverse(changed,data['endpoint_7.json'])
    change('boolean schema version','exact.json',('schema',),True,exact)
    change('diagonal count','exact.json',('diagonal_counts',3),61,exact)
    change('negative startup seed','exact.json',('proposition5','negative_seed'),'0',exact)
    change('uniform normalization','exact.json',('uniform_B','lag'),'-m',exact)
    change('singular-site startup','exact.json',('startup_e',2,2),'1',exact)
    change('rotated lag factor','exact.json',('rotated','lag'),'-(N-h)/(2*(N+h)*(N+h-2))',exact)
    change('exceptional B row zero','exact.json',('memory','B_row0'),'1/n',memory)
    change('third-lag sign','exact.json',('memory','F_sign'),-1,memory)
    change('memory input support','exact.json',('memory','B_input_end'),'n-1',memory)
    change('gauge-memory cancellation','exact.json',('gauge','P_over_j_squared'),'1',v.check_gauge)
    change('sigma3 coefficient','formal_7.json',('D','sigma',3),'8/3',formal)
    change('profile ghost boundary','formal_7.json',('D','f',1,1),'1',formal)
    change('endpoint log coefficient','endpoint_7.json',('D','log_correction',0),'53*a**2/89',endpoint)
    change('endpoint multiplicative coefficient','endpoint_7.json',('D','multiplicative',0),'2',endpoint)
    change('endpoint ratio coefficient','endpoint_7.json',('D','ratio',3),'3/4',endpoint)
    change('inverse logarithmic power','inverse.json',('combined_log_power',),'7/8',inverse)
    change('inverse Taylor correction','inverse.json',('second_correction',),'-53*a**2/(90*L)+3*a**2/L**2+9*a**2/(2*L**3)',inverse)
    change('inverse Newton exponent','inverse.json',('newton_error_X_exponent',),'1-2**k/3',inverse)
    change('truncated coefficient list','formal_7.json',('D','sigma'),['2','0','k'],v.load_formal)
    change('floating-point coefficient','formal_7.json',('D','sigma',3),'2.416666666666667',v.load_formal)
    change('executable expression','formal_7.json',('D','sigma',3),'__import__("os").system("false")',v.load_formal)
    malformed=deepcopy(data['endpoint_7.json']); malformed['D']['unexpected']=[]
    rejection('unknown schema field',lambda:v.load_endpoint(malformed)); cases+=1
    rejection('duplicate JSON key',lambda:v.decode_json('{"D":0,"D":1}','duplicate fixture')); cases+=1
    rejection('nonfinite JSON constant',lambda:v.decode_json('{"D":NaN}','nonfinite fixture')); cases+=1
    for name in v.DATA_NAMES:
        content=(v.ROOT/'data'/name).read_bytes()
        rejection('input bytes '+name,lambda content=content,name=name:v.check_content_pin(content+b'\n',v.PINNED_INPUTS[name],name))
        cases+=1
    changed=deepcopy(data['dependencies.json']); changed['dependencies'][0]['sha256']='0'*64
    rejection('declared relaxed pin',lambda:v.check_dependencies(changed)); cases+=1
    with tempfile.TemporaryDirectory(prefix='dfa-check-negative-') as temporary:
        root=Path(temporary); (root/'dependencies').mkdir()
        for path in v.PINNED_DEPENDENCIES:
            shutil.copyfile(v.REPORT/path,root/path)
        for path in v.PINNED_DEPENDENCIES:
            destination=root/path
            original=destination.read_bytes()
            destination.write_bytes(original+b'corruption')
            rejection('relaxed dependency bytes '+path,lambda:v.check_dependencies(data['dependencies.json'],root))
            destination.write_bytes(original)
            cases+=1
    with tempfile.TemporaryDirectory(prefix='dfa-source-negative-') as temporary:
        root=Path(temporary)
        for name in (*v.SOURCE_NAMES,'manifest.json'):
            target=root/name; target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(v.ROOT/name,target)
        target=root/'verify.py'
        target.write_bytes(target.read_bytes()+b'\n# deliberate corruption\n')
        rejection('checker source bytes',lambda:v.check_package_integrity(root)); cases+=1
    for name in ('verify.py','formal_engine.py','negative_tests.py'):
        tree=ast.parse((v.ROOT/name).read_text(encoding='utf-8'))
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)),f'{name}: Python assert would disappear under -O')
    print(f'PASS all {cases} deliberate corruptions rejected; positive baseline passed; no Python assert statements',flush=True)

if __name__=='__main__':
    try:
        main()
    except (VerificationError,OSError) as error:
        print(f'FAIL: {error}',file=sys.stderr,flush=True)
        sys.exit(1)
