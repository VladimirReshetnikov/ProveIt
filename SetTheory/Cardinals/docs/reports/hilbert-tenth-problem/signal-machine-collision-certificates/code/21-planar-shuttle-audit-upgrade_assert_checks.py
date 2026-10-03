#!/usr/bin/env python3
"""One-time mechanical hardening lineage for the three early audit scripts.
It replaces each assert C, M with if not C: raise RuntimeError(M), using a
condition-derived message when absent. It removes only the previous -O guard.
This tool is idempotent; it does not alter mathematical checks or test cases.
"""
import ast
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
FILES=['independent_audit.py','independent_drift_audit.py','review_parent_code.py']

class ExplicitChecks(ast.NodeTransformer):
    def __init__(self): self.changed=0; self.guards=0
    def visit_Assert(self,node):
        self.changed+=1
        message=node.msg if node.msg is not None else ast.Constant('Audit check failed: '+ast.unparse(node.test))
        return ast.copy_location(ast.If(test=ast.UnaryOp(op=ast.Not(),operand=node.test),
             body=[ast.Raise(exc=ast.Call(func=ast.Name(id='RuntimeError',ctx=ast.Load()),args=[message],keywords=[]),cause=None)],orelse=[]),node)
    def visit_If(self,node):
        if (isinstance(node.test,ast.UnaryOp) and isinstance(node.test.op,ast.Not)
            and isinstance(node.test.operand,ast.Name) and node.test.operand.id=='__debug__'):
            self.guards+=1;return None
        return self.generic_visit(node)

def main():
    records=[]
    for name in FILES:
        path=ROOT/name; before=path.read_bytes(); tree=ast.parse(before)
        transformer=ExplicitChecks(); aftertree=transformer.visit(tree);ast.fix_missing_locations(aftertree)
        if transformer.changed or transformer.guards:
            after=('#!/usr/bin/env python3\n'+ast.unparse(aftertree)+'\n').encode()
            if ast.dump(ast.parse(after),include_attributes=False)!=ast.dump(aftertree,include_attributes=False):
                raise RuntimeError('AST roundtrip changed semantics')
            path.write_bytes(after)
        else: after=before
        if any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(after))):
            raise RuntimeError('An assertion remained after hardening')
        records.append({'file':name,'before_sha256':hashlib.sha256(before).hexdigest(),
                        'after_sha256':hashlib.sha256(after).hexdigest(),
                        'assertions_replaced':transformer.changed,'optimization_guards_removed':transformer.guards})
    output=ROOT/'assert-hardening-lineage.json'
    # Keep the original nontrivial lineage if this idempotent utility is rerun.
    if any(r['assertions_replaced'] or r['optimization_guards_removed'] for r in records):
        output.write_text(json.dumps({'method':'AST-only assert-to-explicit-RuntimeError conversion; check expressions and test cases unchanged. AST roundtrip equality verified.','records':records},indent=2,sort_keys=True)+'\n')
    print(json.dumps(records,indent=2,sort_keys=True))
if __name__=='__main__': main()
