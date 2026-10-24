#!/usr/bin/env python3
"""Independent SymPy audit. No producer or producer polynomial code is imported."""
import ast
import json
import sys
from pathlib import Path
import sympy as s


def require(test, message):
    if not test:
        raise ValueError(message)


def main():
    root = Path(sys.argv[1]).resolve()
    parent = json.loads((root / 'upstream/quartic38.json').read_text())
    names = set(parent['variables'] + parent['fixed_ports'])
    packets = []
    for name in ('octic26', 'decic24'):
        obj = json.loads((root / 'generated' / (name + '.json')).read_text())
        names.update(obj['variables'])
        packets.append(obj)
    symbols = {n: s.Symbol(n) for n in names}

    def parse(text):
        def visit(node):
            if isinstance(node, ast.Expression):
                return visit(node.body)
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return s.Integer(node.value)
            if isinstance(node, ast.Name) and node.id in symbols:
                return symbols[node.id]
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                return -visit(node.operand)
            if isinstance(node, ast.BinOp):
                a, b = visit(node.left), visit(node.right)
                if isinstance(node.op, ast.Add): return a+b
                if isinstance(node.op, ast.Sub): return a-b
                if isinstance(node.op, ast.Mult): return a*b
                if isinstance(node.op, ast.Pow) and b.is_Integer and 0 <= b <= 16:
                    return a**b
            raise ValueError('Unapproved expression node: ' + ast.dump(node))
        return visit(ast.parse(text, mode='eval'))

    src = [parse(x) for x in parent['residuals'][:23]]
    b, J, F, alpha, ac, bc = (symbols[n] for n in ('beta','J','F','alpha','cone_A','cone_B'))
    q = b*J+1
    C = q-F-alpha
    G = ac*F*bc*C-(q-ac*F-bc*C)**2
    Z = symbols['eta']*symbols['zeta']
    t, g1, g2, g3 = (symbols[n] for n in ('pair_root','guard1','guard2','guard3'))
    joint = G*Z-(t*t-G-Z+1)**2-1-g1*g1-g2*g2-g3*(g3+1)
    src.append(joint)
    results = []
    for obj in packets:
        vs = [symbols[n] for n in obj['variables']]
        rows = [s.expand(parse(x)) for x in obj['residuals']]
        restores = {symbols[k]:parse(v) for k,v in obj['source_joint_restoration'].items()}
        used = []
        zero_count = 0
        for i, row in enumerate(src):
            restored = s.expand(row.xreplace(restores))
            if restored == 0:
                zero_count += 1
                continue
            hits = [j for j,new in enumerate(rows) if restored == new or restored == -new]
            require(len(hits)==1, f'{obj["name"]}: source row {i} did not restore')
            used.append(hits[0])
        require(sorted(used)==list(range(len(rows))), 'All residuals must restore exactly once')
        degrees = [s.Poly(row,*vs).total_degree() for row in rows]
        require(2*max(degrees)==obj['exact_degree'], 'Total-degree upper bound')
        # Compute the exact lower-bound coefficient rowwise; no giant full
        # sum-of-squares expansion is required for this independent check.
        if obj['name']=='octic26':
            monomial = symbols['pair_root']**8
            target = 1
        else:
            monomial = symbols['r']**2*symbols['a']**4*symbols['eta']**4
            target = 4
        # Coordinates absent from the target monomial can be set to zero.
        target_vars = sorted(monomial.free_symbols, key=str)
        zeros = {v:0 for v in vs if v not in target_vars}
        coefficient = sum(s.Poly(s.expand(row.xreplace(zeros)**2),*target_vars)
                          .coeff_monomial(monomial) for row in rows)
        require(s.expand(coefficient)==target, 'Exact actual-port-independent degree witness')
        require(len(vs)==obj['variable_count'], 'Variable count')
        results.append({'name':obj['name'],'variables':len(vs),'residuals':len(rows),
                        'residual_degrees':degrees,'exact_degree':obj['exact_degree'],
                        'restored_source_rows':len(src),'identically_zero_rows':zero_count,
                        'leading_monomial':str(monomial),'exact_coefficient':target})
    report = {'status':'PASS','engine':'independent SymPy '+s.__version__,
              'producer_code_imported':False,'results':results,
              'scope':'Exact row identities and degree evidence only. Universal existence equivalences use the written proofs.'}
    output = root / 'certificates' / 'ROOT_INDEPENDENT_AUDIT.json'
    output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main()
