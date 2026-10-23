#!/usr/bin/env python3
"""Independent exact algebra audit; imports no component builder."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def audit():
    packet = json.loads((ROOT / 'quartic42.json').read_text())
    names = packet['variables'] + packet['fixed_numerals']
    count = len(packet['variables'])
    zero = (0,) * len(names)
    def con(n):
        return {zero: n} if n else {}
    def add(a, b, sign=1):
        out = dict(a)
        for monomial, coefficient in b.items():
            out[monomial] = out.get(monomial, 0) + sign * coefficient
            if not out[monomial]: del out[monomial]
        return out
    def mul(a, b):
        out = {}
        for m, c in a.items():
            for n, d in b.items():
                e = tuple(x+y for x,y in zip(m,n))
                out[e] = out.get(e, 0) + c*d
        return {e:c for e,c in out.items() if c}
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return con(node.value)
        if isinstance(node, ast.Name):
            exponent = [0] * len(names)
            exponent[names.index(node.id)] = 1
            return {tuple(exponent): 1}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return {e:-c for e,c in visit(node.operand).items()}
        if isinstance(node, ast.BinOp):
            left = visit(node.left)
            if isinstance(node.op, ast.Pow):
                if not isinstance(node.right, ast.Constant): raise ValueError('nonliteral power')
                power = node.right.value
                if type(power) is not int or power < 0: raise ValueError('invalid power')
                result = con(1)
                for _ in range(power): result = mul(result, left)
                return result
            right = visit(node.right)
            if isinstance(node.op, ast.Add): return add(left, right)
            if isinstance(node.op, ast.Sub): return add(left, right, -1)
            if isinstance(node.op, ast.Mult): return mul(left, right)
        raise ValueError('unsupported expression')
    def parse(text): return visit(ast.parse(text, mode='eval').body)
    residuals = [parse(t) for t in packet['residuals']]
    if count != 42 or len(residuals) != 27: raise ValueError('wrong sizes')
    degrees = [max(sum(e[:count]) for e in r) for r in residuals]
    if max(degrees) != 2: raise ValueError('nonquadratic')
    total = con(0)
    for r in residuals: total = add(total, mul(r,r))
    degree = max(sum(e[:count]) for e in total)
    tau4 = [0] * len(names)
    tau4[names.index('tau')] = 4
    if degree != 4 or total.get(tuple(tau4)) != 1: raise ValueError('degree certificate')
    used = {names[i] for r in residuals for e in r for i,v in enumerate(e) if v}
    if used != set(names): raise ValueError('unused inputs')
    scale = parse('w - 4*u**2')
    guard = parse('eta*zeta - 1 - EZ_pos1**2 - EZ_pos2**2 - EZ_pos3*(EZ_pos3+1)')
    if residuals[22] != scale or residuals[26] != guard: raise ValueError('new residual mismatch')
    parent = json.loads((ROOT/'upstream'/'quartic45.json').read_text())
    old_retained = parent['residuals'][:22] + parent['residuals'][25:28]
    new_retained = packet['residuals'][:22] + packet['residuals'][23:26]
    if any(parse(a) != parse(b) for a,b in zip(old_retained,new_retained)):
        raise ValueError('changed inherited residual')
    result = dict(audit='Independent AST sparse-integer expansion; no builder import',
        unknowns=count, fixed_ports=len(packet['fixed_numerals']), residuals=len(residuals),
        residual_degrees=degrees, exact_total_degree=degree,
        terms_with_ports_symbolic=len(total), tau_fourth_power_coefficient=1,
        all_inputs_used=True, unchanged_inherited_residuals=25,
        two_changed_residuals_checked=True,
        polynomial_sha256=hashlib.sha256((ROOT/'quartic42.json').read_bytes()).hexdigest(),
        boundary='Exact finite algebra only; the universal argument is in PROOF.md and its inherited dependencies.')
    (ROOT/'INDEPENDENT_ALGEBRA.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__': audit()
