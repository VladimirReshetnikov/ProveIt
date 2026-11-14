#!/usr/bin/env python3
"""Check that retained induction rules match the archived U214 implementation."""
import ast,json,zipfile
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)
def defs(source):
    return {n.name:n for n in ast.parse(source).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
def assignments(source):
    return {n.targets[0].id:n.value for n in ast.parse(source).body
            if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)}
class Header(ast.NodeTransformer):
    def visit_Constant(self,n):
        return ast.Name(id='HEADER_BASE',ctx=ast.Load())if n.value==64 else n
def audit(root):
    root=Path(root);z=zipfile.ZipFile(root/'inputs/U214_ConPA_Reduction_2026-10-28.zip')
    prefix='U214_ConPA_Reduction_2026-10-28/code/runtime/'
    old_text=z.read(prefix+'symbolic_runtime.py').decode();new_text=(root/'code/symbolic_runtime.py').read_text()
    old=defs(old_text);new=defs(new_text)
    old.pop('main');old.pop('validate_inputs');need(set(old)==set(new),'induction engine interface')
    for name,n in old.items():
        if name=='case':n=Header().visit(n)
        need(ast.dump(n,include_attributes=False)==ast.dump(new[name],include_attributes=False),'changed induction rule: '+name)
    olds=defs(z.read(prefix+'independent_runtime.py').decode());news=defs((root/'code/independent_runtime.py').read_text())
    need(set(news)=={'table','inc','strip'},'helper interface')
    for name,n in news.items():need(ast.dump(n,include_attributes=False)==ast.dump(olds[name],include_attributes=False),'changed helper '+name)
    oa,na=assignments(old_text),assignments(new_text)
    for name in ('NV','ZERO','BLANK'):
        need(ast.dump(oa[name],include_attributes=False)==ast.dump(na[name],include_attributes=False),'changed engine constant '+name)
    op=assignments(z.read(prefix+'independent_runtime.py').decode())['PHY']
    np=assignments((root/'code/independent_runtime.py').read_text())['PHY']
    need(ast.dump(op,include_attributes=False)==ast.dump(np,include_attributes=False),'changed register permutation')
    env={}
    for n in ast.parse((root/'code/symbolic_runtime.py').read_text()).body:
        if isinstance(n,ast.Assign)and len(n.targets)==1 and isinstance(n.targets[0],ast.Name)and n.targets[0].id in ('HEADER_BASE','NV'):
            env[n.targets[0].id]=ast.literal_eval(n.value)
    need(env=={'HEADER_BASE':56,'NV':13},'affine/header dimensions')
    return {'status':'ARCHIVED_INDUCTION_RULES_MATCH','engine_definitions':sorted(new),'retained_helpers':sorted(news),'matched_constants':['NV','ZERO','BLANK','PHY'],'header_base':56,'changes':'Replace the two initial/target header constants in case by HEADER_BASE; set parameter to 56; omit obsolete CLI/source pins and unused helper routines. Core inference bodies otherwise match.'}
if __name__=='__main__':print(json.dumps(audit(Path(__file__).resolve().parents[1]),indent=2))
