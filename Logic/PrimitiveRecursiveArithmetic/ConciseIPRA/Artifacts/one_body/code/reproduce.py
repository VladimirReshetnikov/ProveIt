"""Measure complete standalone modules and run independent certificate checks."""
from pathlib import Path
import ast
import gzip
import hashlib
import importlib.util
import io
import itertools
import json
import platform
import random
import subprocess
import sys
import tokenize

ROOT=Path(__file__).resolve().parent
FILES=['checker_clausal_control.py','checker_one_body.py','checker_native_control.py','checker_native_pareto.py','checker_native_refined.py','baseline_compact_516.py']

def metric(name):
    raw=(ROOT/name).read_bytes()
    normalized=(ast.unparse(ast.parse(raw.decode('utf-8')))+'\n').encode('utf-8')
    ignored={tokenize.ENCODING,tokenize.NEWLINE,tokenize.NL,tokenize.INDENT,tokenize.DEDENT,tokenize.COMMENT,tokenize.ENDMARKER}
    return {'file':name,'raw_bytes':len(raw),'normalized_bytes':len(normalized),
            'significant_tokens':sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
            'ast_nodes':len(list(ast.walk(ast.parse(normalized.decode())))),
            'gzip9_normalized_bytes':len(gzip.compress(normalized,compresslevel=9,mtime=0)),
            'source_sha256':hashlib.sha256(raw).hexdigest(),'normalized_sha256':hashlib.sha256(normalized).hexdigest()}

def run(checker,data,optimized=False):
    args=[sys.executable]+(['-O'] if optimized else [])+[str(ROOT/checker)]
    result=subprocess.run(args,input=data,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=20)
    return result.returncode==0 and result.stdout.strip()==b'ACCEPT'

def load_function(path,name):
    tree=ast.parse((ROOT/path).read_text())
    fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name==name)
    namespace={}
    exec(compile(ast.Module(body=[fn],type_ignores=[]),str(ROOT/path),'exec'),namespace)
    return namespace[name]

def truth_of_validator(fn,a,d):
    try: return bool(fn(a,d))
    except Exception: return False

# Validation is tested independently of proof acceptance; exceptions count as
# rejection, as they do at the standalone interface.
v0=load_function('checker_native_control.py','v')
v1=load_function('checker_native_refined.py','v')
v2=load_function('checker_native_pareto.py','v')
atoms=[None,False,True,-3,-1,0,1,2,3,4,5,7,0.0,1.0,float('nan'),float('inf'),'','0',{}, {'a':0}]
values=list(atoms)
for n in range(4): values.extend(list(p) for p in itertools.product(atoms,repeat=n))
rng=random.Random(20261111)
for _ in range(1000):
    values.append([rng.choice(values) for _ in range(rng.randrange(4))])
validator_checks=0
for value in values:
    for d in (0,1):
        assert truth_of_validator(v0,value,d)==truth_of_validator(v1,value,d)==truth_of_validator(v2,value,d)
        validator_checks+=1

# Each generated proof is checked in a separate ordinary and optimized Python
# process. The -O run verifies that the actual checkers do not rely on assert.
manifest=json.loads((ROOT/'example_manifest.json').read_text())
proof_runs=[]
for item in manifest:
    checker='checker_clausal_control.py' if '/control/' in item['file'] else 'checker_one_body.py'
    data=(ROOT/item['file']).read_bytes()
    for optimized in (False,True):
        accepted=run(checker,data,optimized)
        assert accepted==item['accept'],(item,optimized,accepted)
        proof_runs.append({'checker':checker,'certificate':item['file'],'optimized':optimized,'accepted':accepted})

native_runs=[]
for path in sorted((ROOT/'examples/native').glob('*.json')):
    data=path.read_bytes()
    for optimized in (False,True):
        old=run('checker_native_control.py',data,optimized)
        new=run('checker_native_refined.py',data,optimized)
        pareto=run('checker_native_pareto.py',data,optimized)
        assert old==new==pareto,(path.name,optimized,old,new,pareto)
        if path.stem.startswith(('reject_','false_','future_','context_','scalar_false_','unproved_')):
            assert not old,(path.name,'invalid proof unexpectedly accepted')
        native_runs.append({'certificate':str(path.relative_to(ROOT)),'optimized':optimized,'control_accept':old,'candidate_accept':new,'pareto_accept':pareto})

spec=importlib.util.spec_from_file_location('gate_audit',ROOT/'audit_gate_scopes.py')
audit=importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
gate=audit.check(ROOT/'checker_one_body.py')
metrics={'python':platform.python_version(),'implementation':platform.python_implementation(),
         'normalization':'ast.unparse(ast.parse(complete_module)) plus one LF; no source removed',
         'gzip':'gzip.compress(normalized, compresslevel=9, mtime=0); informational only',
         'modules':[metric(name) for name in FILES]}
results={'status':'PASS','validator_cases':validator_checks,'validator_comparisons':2*validator_checks,'gate_audit':gate,
         'one_body_and_control_certificates':len(manifest),'standalone_proof_process_runs':len(proof_runs),
         'accepted_proof_process_runs':sum(x['accepted'] for x in proof_runs),
         'rejected_proof_process_runs':sum(not x['accepted'] for x in proof_runs),
         'native_fixture_cases':len(native_runs),'native_process_runs':3*len(native_runs),
         'proof_runs':proof_runs,'native_runs':native_runs,
         'limits':'Finite tests support the implementation. They are not proof-assistant verification or a proof of universal soundness/completeness. Mathematical proofs are supplied in the report.'}
(ROOT/'metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
(ROOT/'results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({k:v for k,v in results.items() if k not in ('proof_runs','native_runs','limits')},indent=2))
print(json.dumps(metrics,indent=2))
