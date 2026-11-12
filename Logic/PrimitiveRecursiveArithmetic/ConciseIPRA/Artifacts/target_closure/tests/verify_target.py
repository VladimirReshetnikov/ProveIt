import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tests'))
import generate_target
cases,open_cases=generate_target.build()
spec=importlib.util.spec_from_file_location('target_kernel',ROOT/'code/target_checker.py')
kernel=importlib.util.module_from_spec(spec);spec.loader.exec_module(kernel)

receipts=[]
for case in cases:
    raw=(ROOT/'tests/target'/case['file']).read_bytes()
    for optimized in [False,True]:
        process=subprocess.run([sys.executable]+(['-O'] if optimized else [])+[str(ROOT/'code/target_checker.py')],input=raw,capture_output=True,timeout=8)
        accepted=process.returncode==0 and process.stdout==b'ACCEPT\n'
        if accepted!=case['accept']:
            raise RuntimeError((case['file'],optimized,accepted,process.stderr.decode()))
        receipts.append(dict(file=case['file'],optimized=optimized,accept=accepted))

open_receipts=[]
for case in open_cases:
    scope=case['scope']
    assert kernel.formula(case['goal'],scope)
    assert all(kernel.formula(f,scope) for f in case['context'])
    try:
        accepted=kernel.derive(case['proof'],tuple(case['context']),scope)==case['goal']
    except (ValueError,TypeError,IndexError,RecursionError):
        accepted=False
    assert accepted==case['accept'],case['name']
    open_receipts.append(dict(name=case['name'],accept=accepted,note=case['note']))

g=generate_target.g
rng=random.Random(112026)
serial=0
def fresh():
    global serial
    serial+=1
    return 'bound_'+str(serial)
def term(depth,env):
    if depth==0 or rng.randrange(3)==0:
        return rng.choice([0]+list(env))
    if rng.randrange(2):
        return g.S(term(depth-1,env))
    u=fresh()
    return g.I(term(depth-1,env),term(depth-1,env),u,term(depth-1,(u,)+env))
def formula(depth,env):
    if depth==0 or rng.randrange(3)==0:
        return g.Eq(term(2,env),term(2,env))
    if rng.randrange(2):
        y=fresh()
        return g.Q(y,formula(depth-1,(y,)+env))
    x,y=fresh(),fresh()
    return g.D(x,y,formula(depth-1,(y,x)+env))
def replace_x(tree,value):
    if tree=='x':
        return value
    if type(tree) is tuple:
        return tuple(replace_x(t,value) for t in tree)
    return tree

substitution_checks=0
for _ in range(300):
    f=formula(3,('x','p','q'))
    value=term(3,('p','q'))
    encoded=g.fe(f,('x','p','q'))
    expected=g.fe(replace_x(f,value),('p','q'))
    assert kernel.substitute(encoded,0,g.te(value,('p','q')))==expected
    assert kernel.lift(encoded)==g.fe(f,('unused','x','p','q'))
    substitution_checks+=2

result=dict(closed_cases=len(cases),process_executions=len(receipts),open_cases=len(open_receipts),substitution_checks=substitution_checks,mismatches=0,closed_results=receipts,open_results=open_receipts,
    qualification='These finite checks verify implementation examples and regressions. They do not prove soundness, completeness, bi-interpretability, or absolute minimality. Open contradictory assumptions are never presented as closed theorems.')
(ROOT/'evidence/target_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if not k.endswith('_results')},indent=2))
