#!/usr/bin/env python3
"""Recompute the retained-function AST audit; no reference module is executed."""
from pathlib import Path
import argparse,ast,copy,hashlib,json

ROOT=Path(__file__).resolve().parents[1]
RUNTIME=['State','add','bit','block','case','file_bits','minus1','neg','nonnegative',
         'normal','num','prove_blocks','rev','run','tail','var']
SUPPORT=['inc','strip','table']

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def definitions(p):
    t=ast.parse(p.read_text())
    return {n.name:n for n in t.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))},t
def require(ok,msg):
    if not ok:raise ValueError(msg)
def dump(n):return ast.dump(n,include_attributes=False)
def assignment(tree,name):
    found=[n.value for n in tree.body if isinstance(n,ast.Assign) and
           any(isinstance(v,ast.Name) and v.id==name for v in n.targets)]
    require(len(found)==1,'Expected unique constant '+name)
    return found[0]

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'reproduced/engine_extraction_audit.json');a=p.parse_args()
    ref=ROOT/'upstream/proveit';kernels=ROOT/'verification/kernels'
    old,oldtree=definitions(ref/'symbolic_runtime_reference.py')
    new,newtree=definitions(kernels/'runtime_engine.py')
    require(set(new)==set(RUNTIME),'Unexpected retained runtime definitions')
    block=copy.deepcopy(old['prove_blocks'])
    sig=[n for n in ast.walk(block) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='signatures' for t in n.targets)]
    require(len(sig)==1,'Expected one signature assignment')
    require(ast.literal_eval(sig[0].value)==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'Unexpected reference signatures')
    sig[0].value=ast.parse("[(64,1,'B','B'),(95,1,'B','C'),(40,-1,'B','B'),(97,-1,'C','B')]",mode='eval').body
    old['prove_blocks']=block
    for name in RUNTIME:require(dump(old[name])==dump(new[name]),'Runtime AST differs: '+name)
    for name in ['NV','ZERO','BLANK']:require(dump(assignment(oldtree,name))==dump(assignment(newtree,name)),'Constant differs: '+name)
    os,ost=definitions(ref/'independent_runtime_reference.py');ns,nst=definitions(kernels/'runtime_support.py')
    require(set(ns)==set(SUPPORT),'Unexpected retained support definitions')
    for name in SUPPORT:require(dump(os[name])==dump(ns[name]),'Support AST differs: '+name)
    require(dump(assignment(ost,'PHY'))==dump(assignment(nst,'PHY')),'Physical permutation differs')
    record={'status':'RECOMPUTED_ENGINE_EXTRACTION_AST_PASS','runtime_definitions':RUNTIME,
            'support_definitions':SUPPORT,'constant_definitions_checked':['NV','ZERO','BLANK','PHY'],
            'sole_function_change':'prove_blocks signatures 73->64,95->95,48->40,112->97; every resulting block schema is rederived from the actual table',
            'reference_engine_sha256':sha(ref/'symbolic_runtime_reference.py'),
            'reference_support_sha256':sha(ref/'independent_runtime_reference.py'),
            'runtime_engine_sha256':sha(kernels/'runtime_engine.py'),
            'runtime_support_sha256':sha(kernels/'runtime_support.py'),
            'reference_code_executed':False}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__=='__main__':main()
