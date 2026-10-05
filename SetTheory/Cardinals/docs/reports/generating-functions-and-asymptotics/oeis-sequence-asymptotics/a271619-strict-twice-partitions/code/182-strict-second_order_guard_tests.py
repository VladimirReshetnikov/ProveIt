#!/usr/bin/env python3
"""Corrupt every scalar leaf and scope of the exact second-order certificate."""
import ast
import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT/'code'))
import verify
import verify_second_order as verifier
import second_order as exact


def leaves(value,path=()):
    if type(value) is dict:
        for key,child in sorted(value.items()):
            yield from leaves(child,path+(key,))
    elif type(value) is list:
        for index,child in enumerate(value):
            yield from leaves(child,path+(index,))
    else:
        yield path,value


def main():
    expected=verifier.derive()
    verify.same(expected,verify.load_certificate(ROOT/'data/second_order_certificate.json'))
    rejected=[]
    def bad(label,call):
        try:call()
        except (ValueError,RuntimeError,TypeError,KeyError,IndexError,OSError):
            rejected.append(label)
            return
        raise ValueError('expected rejection did not occur: '+label)
    mutants=[]
    for path,value in leaves(expected):
        changed=copy.deepcopy(expected);target=changed
        for key in path[:-1]:target=target[key]
        target[path[-1]]=(not value if type(value) is bool else value+1 if type(value) is int else str(value)+'#corrupt')
        mutants.append((repr(path),json.dumps(changed)))
    for label,edit in [('missing field',lambda d:d.pop('A2')),('extra field',lambda d:d.__setitem__('extra',0)),
        ('float report',lambda d:d.__setitem__('report',182.0)),
        ('integer scope',lambda d:d['scope'].__setitem__('exact_finite_quasimodular_reconstruction',1)),
        ('missing monomial',lambda d:d['A2'].pop()),
        ('noncanonical rational',lambda d:d['A2'][0].__setitem__('coefficient','-18/20'))]:
        changed=copy.deepcopy(expected);edit(changed);mutants.append((label,json.dumps(changed)))
    mutants += [('duplicate','{"report":182,'+json.dumps(expected)[1:]),('nested duplicate','{"a":{"x":1,"x":2}}'),
                ('NaN','{"x":NaN}'),('Infinity','{"x":Infinity}'),('trailing','{} {}'),('invalid','{'),('array','[]')]
    with tempfile.TemporaryDirectory(prefix='report182-second-guards-') as temp:
        root=Path(temp);badfile=root/'bad.json'
        for label,text in mutants:
            badfile.write_text(text)
            bad(label,lambda:verify.same(verify.load_certificate(badfile),expected))
        refs=root/'references'
        for name in verifier.PINS:
            path=refs/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((ROOT/name).read_bytes())
        with mock.patch.object(verifier,'ROOT',refs):
            verifier.references()
            for name in verifier.PINS:
                path=refs/name;old=path.read_bytes();path.write_bytes(old+b'corruption')
                bad('pin '+name,verifier.references);path.write_bytes(old)
        badfile.write_text(mutants[0][1]);out,err=io.StringIO(),io.StringIO()
        with mock.patch.object(sys,'argv',['verify_second_order.py','--data',str(badfile)]), \
             contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
            result=verifier.main()
        verify.need(result==1 and 'SECOND-ORDER VERIFICATION FAILED:' in err.getvalue(),'corrupt CLI accepted')
    bad('runtime guard',lambda:exact.need(False,'negative control'))
    for matrix,rhs in [([],[]),([[1,2]],[1]),([[0]],[1]),([[1,2],[2,4]],[1,2])]:
        bad('invalid matrix '+str(matrix),lambda matrix=matrix,rhs=rhs:exact.solve(matrix,rhs))
    solution,determinant=exact.solve([[0,1],[2,3]],[1,5])
    verify.need(solution==[1,1] and determinant==-2,'pivot swap determinant')
    for exponent in (-1,True,1.0,'1'):
        bad('bad power '+repr(exponent),lambda exponent=exponent:exact.power([1]+[0]*20,exponent))
        bad('bad polynomial power '+repr(exponent),lambda exponent=exponent:exact.pow_poly({(0,):1},exponent,1))
    bad('series length',lambda:exact.multiply([1],[1]))
    bad('polynomial basis mismatch',lambda:exact.mul({(0,):1},{(0,0):1}))
    for name in ('code/second_order.py','code/verify_second_order.py','second_order_guard_tests.py'):
        tree=ast.parse((ROOT/name).read_text())
        verify.need(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)),'removable assertion')
        if name=='code/second_order.py':
            verify.need(not any(isinstance(node,ast.Constant) and type(node.value) is float for node in ast.walk(tree)),'float literal in core')
    print(json.dumps({'status':'PASS','report':182,'scalar_leaves_mutated':len(list(leaves(expected))),
        'corrupt_certificate_variants':len(mutants),'negative_rejections':len(rejected),
        'normal_optimized_runtime_guards':True,'pivot_swap_determinant_checked':True},sort_keys=True))


if __name__=='__main__':
    try:main()
    except Exception as exc:
        print('SECOND-ORDER GUARD FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
