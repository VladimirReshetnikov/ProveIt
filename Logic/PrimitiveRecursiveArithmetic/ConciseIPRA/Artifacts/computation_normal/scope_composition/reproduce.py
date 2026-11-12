from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import ast
import gzip
import io
import json
import random
import subprocess
import sys
import tokenize

ROOT=Path(__file__).resolve().parent
PROGRAMS=[ROOT/'reference/typed870.py',ROOT/'code/checker.py']
CASES=json.loads((ROOT/'tests/cases.json').read_text())
# Extra type attacks inside an unused prefix. Both gates inspect the whole input.
good=next(r['input'] for r in CASES if r['name']=='native_computation')
for item in [float('nan'),float('inf'),float('-inf'),[False],[0.0],[''],{'0':0}]:
    CASES.append({'name':'extra_prefix_'+repr(item),'input':[item]+good,'expected':False})


def run(job):
    program,row,optimized=job
    cmd=[sys.executable,'-I','-S','-B']+(['-O'] if optimized else [])+[str(program)]
    r=subprocess.run(cmd,input=json.dumps(row['input']).encode(),capture_output=True,timeout=20)
    ok=r.returncode==0 and r.stdout==b'ACCEPT\n'
    return {'program':program.relative_to(ROOT).as_posix(),
            'case':row['name'],'optimized':optimized,'expected':row['expected'],
            'accepted':ok,'passed':ok==row['expected']}

jobs=[(program,row,optimized) for program in PROGRAMS for row in CASES for optimized in (False,True)]
with ThreadPoolExecutor(max_workers=4) as pool:
    processes=list(pool.map(run,jobs))

class ProofBoundary(Exception):pass

def boundary():raise ProofBoundary

def definitions(path):
    module=ast.parse(path.read_text())
    functions=ast.Module([x for x in module.body if isinstance(x,ast.FunctionDef)],[])
    ns={}
    exec(compile(functions,str(path),'exec'),ns)
    ns['q']=boundary
    return ns

old,new=map(definitions,PROGRAMS)
def preflight(ns,value):
    try:
        if not ns['v'](value):return False
        ns['c'](value)
        return True
    except ProofBoundary:
        return True
    except (ValueError,TypeError,IndexError,RecursionError,AttributeError):
        return False

rng=random.Random(120311)

def term(depth,scope,valid):
    if depth==0 or rng.randrange(3)==0:
        return rng.choice([0]+list(range(3,scope,2))) if valid else rng.randrange(-3,40)
    arity=rng.choice([1,3])
    return [term(depth-1,scope+5-arity,valid) for _ in range(arity)]

def formula(depth,scope=0,valid=False):
    if depth==0 or rng.randrange(3)==0:
        return [term(3,scope+3,valid) for _ in range(2)]
    arity=rng.choice([1,3]);body=formula(depth-1,scope+5-arity,valid)
    return [body]*arity

def raw(depth):
    if depth==0 or rng.randrange(3)==0:return rng.randrange(-3,40)
    return [raw(depth-1) for _ in range(rng.randrange(5))]

samples=[raw(4) for _ in range(3000)]
samples += [formula(4,valid=False) for _ in range(3000)]
samples += [formula(4,valid=True) for _ in range(3000)]
checks=[]
for i,x in enumerate(samples):
    a=preflight(old,x);b=preflight(new,x)
    if a!=b:checks.append({'index':i,'goal':x,'baseline':a,'new':b})
metrics=[]
for program in PROGRAMS:
    normalized=(ast.unparse(ast.parse(program.read_bytes()))+'\n').encode()
    ts=[t for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
        if t.type not in (tokenize.ENDMARKER,tokenize.ENCODING,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT)]
    metrics.append({'file':str(program.relative_to(ROOT)),'normalized_bytes':len(normalized),
                    'tokens':len(ts),'ast_nodes':sum(1 for _ in ast.walk(ast.parse(normalized))),
                    'gzip9':len(gzip.compress(normalized,compresslevel=9,mtime=0))})
report={'python':sys.version,'fixture_count':len(CASES),'process_count':len(processes),
        'process_failures':[r for r in processes if not r['passed']],
        'scope_preflight_comparisons':len(samples),'scope_preflight_differences':checks,
        'metrics':metrics,'processes':processes}
(ROOT/'evidence/verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='processes'},indent=2))
if report['process_failures'] or checks:raise SystemExit(1)
