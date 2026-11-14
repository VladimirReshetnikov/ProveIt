#!/usr/bin/env python3
"""Independent symbolic binding of the exact exchanged AX macro interval."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent.parent


def expand(path):
    grammar = json.loads(path.read_text())
    def visit(node):
        if isinstance(node,str) and node in grammar['rules']:
            return visit(grammar['rules'][node])
        if node == 'node60':
            return [['leaf','inc',1]]*2
        if node == 'node61':
            return [['leaf','inc',1]]*4
        if isinstance(node,list) and len(node) == 2:
            return visit(node[0])+visit(node[1])
        return [node]
    return visit(grammar['root'])


def execute(block):
    stack, top = [], 'old_T'
    variables = {'node55':'D','node58':'H','node70':'A'}
    for token in block:
        if isinstance(token,str) and token in variables:
            stack.append(top)
            top = variables[token]
        elif token == 'node65':
            assert stack
            top = ('pair4',stack.pop(),top,0)
        else:
            assert token == ['leaf','inc',1]
            assert isinstance(top,tuple) and top[0] == 'pair4'
            top = (*top[:3],top[3]+1)
    return stack,top


def I(a,b):
    return ('I',a,b)


def U(i,a):
    return ('U',i,a)


def raw(formula):
    if isinstance(formula,str):
        return formula
    op,a,b = formula
    return (('pair4',raw(a),raw(b),0) if op == 'I'
            else ('pair4',raw(b),raw(a),2))


def number(formula,environment):
    if isinstance(formula,str):
        return environment[formula]
    op,a,b = formula
    a,b = number(a,environment),number(b,environment)
    if op == 'U':
        a,b = b,a
    return 4*((a+b)*(a+b+1)//2+b)+(2 if op == 'U' else 0)


if __name__ == '__main__':
    assert __debug__
    old = expand(ROOT/'construction/inputs/pa194.grammar.json')
    new = expand(ROOT/'construction/inputs/q.grammar.json')
    assert len(old) == len(new) == 190
    assert old[:102] == new[:102] and old[121:] == new[121:]
    P,Q,R = U('D','A'),U('D',I('A','H')),U('D','H')
    f_old,f_new = I(P,I(Q,R)),I(Q,I(P,R))
    assert execute(old[102:121]) == (['old_T'],raw(f_old))
    assert execute(new[102:121]) == (['old_T'],raw(f_new))
    env = {'A':1,'D':0,'H':0}
    a,b = number(f_old,env),number(f_new,env)
    assert a != b
    result = {'status':'PASS','macro_tokens':190,'changed_interval':[102,121],
              'all_surrounding_tokens_identical':True,'stack_effect_identical':True,
              'old_formula':f_old,'new_formula':f_new,
              'example_parameters':env,'old_code':a,'new_code':b}
    (ROOT/'evidence/exchange_binding.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
