"""Check that a checker pair has exactly the proved direct-binding rewrite.

Usage: python3 audit_equivalence.py compact OLD.py NEW.py
       python3 audit_equivalence.py strict OLD.py NEW.py

This is a syntactic witness for the accompanying semantics argument.
It does not execute arbitrary certificates or prove Python semantics.
"""
import argparse
import ast
import copy
import hashlib
import json
from pathlib import Path


def same(left, right):
    return ast.dump(left) == ast.dump(right)


def audit(style, old_path, new_path):
    old_bytes = Path(old_path).read_bytes()
    new_bytes = Path(new_path).read_bytes()
    old = ast.parse(old_bytes)
    new = ast.parse(new_bytes)
    old_outer = old.body[1]
    new_outer = new.body[1]
    assert isinstance(new_outer, ast.Assign)
    assert same(new_outer.targets[0], ast.Name(id='c', ctx=ast.Store()))
    assert len(new_outer.targets) == 1
    new_lambda = new_outer.value
    assert isinstance(new_lambda, ast.Lambda)
    if style == 'compact':
        assert isinstance(old_outer, ast.Assign)
        assert same(old_outer.targets[0], new_outer.targets[0])
        assert len(old_outer.targets) == 1
        old_lambda = old_outer.value
        assert isinstance(old_lambda, ast.Lambda)
        assert isinstance(old_lambda.body, ast.BoolOp)
        assert isinstance(old_lambda.body.op, ast.And)
        assert len(old_lambda.body.values) == 2
        assignment, old_body = old_lambda.body.values
        old_args = old_lambda.args
    else:
        assert isinstance(old_outer, ast.FunctionDef)
        assert old_outer.name == 'c'
        assert not old_outer.decorator_list
        assert old_outer.returns is None
        assert old_outer.type_comment is None
        assert not old_outer.type_params
        assert len(old_outer.body) == 2
        assign, ret = old_outer.body
        assert isinstance(assign, ast.Assign) and len(assign.targets) == 1
        assert same(assign.targets[0], ast.Name(id='i', ctx=ast.Store()))
        assert isinstance(ret, ast.Return)
        assignment = ast.NamedExpr(target=copy.deepcopy(assign.targets[0]),
                                   value=copy.deepcopy(assign.value))
        old_body = ret.value
        old_args = old_outer.args
    inverse = copy.deepcopy(new_lambda.body)
    assert isinstance(inverse, ast.BoolOp) and isinstance(inverse.op, ast.Or)
    assert len(inverse.values) == 2
    first = inverse.values[0]
    assert isinstance(first, ast.Compare)
    call = first.left
    assert isinstance(call, ast.Call)
    new_assignment = call.func
    assert isinstance(new_assignment, ast.NamedExpr)
    call.func = ast.Name(id='i', ctx=ast.Load())
    checks = {
        'parameters_equal': same(old_args, new_lambda.args),
        'assigned_lambda_equal': same(assignment, new_assignment),
        'remaining_expression_equal': same(old_body, inverse),
        'other_module_statements_equal': same(
            ast.Module(body=old.body[:1] + old.body[2:], type_ignores=[]),
            ast.Module(body=new.body[:1] + new.body[2:], type_ignores=[])),
    }
    assert all(checks.values()), checks
    return {'style': style, 'baseline': str(old_path), 'candidate': str(new_path),
            'baseline_sha256': hashlib.sha256(old_bytes).hexdigest(),
            'candidate_sha256': hashlib.sha256(new_bytes).hexdigest(), **checks}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('style', choices=('compact', 'strict'))
    parser.add_argument('baseline')
    parser.add_argument('candidate')
    args = parser.parse_args()
    print(json.dumps(audit(args.style, args.baseline, args.candidate), indent=2))
