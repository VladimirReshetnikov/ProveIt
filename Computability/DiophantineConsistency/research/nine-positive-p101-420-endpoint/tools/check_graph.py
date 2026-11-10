#!/usr/bin/env python3
"""Binding checker for the Lean literal of package 101's 420-operation boundary_simple equation.

Checks (standard library only):
  1. Nine121/N101p420Graph.lean is byte-identical to a fresh run of generate_n101p420_graph.py,
     whose own numeric gate (exact arithmetic modulo 2^127 - 1 at random points) verifies every
     closed form, every register formula and output = N9Finalizer.value(prefix) on the JSON DAG;
  2. gate by gate, independently of the generator: every `def n<i>` of the Lean file is parsed
     back (variable index, integer literal, scale leaf, port polynomial of a coefficient leaf, or
     operation with its two children) and compared with node i of the pinned JSON;
  3. IPRANine101p420.expression is node 451 at Mixed121Ports.ports;
  4. rejected mutations: a changed child, operation, literal, variable, coefficient recipe and
     scale in the parsed literal are each detected by the comparison, and a changed JSON literal
     changes the output modulo the prime (so the numeric gate of 1. is sensitive).
Writes CHECK_GRAPH.json next to the record README.
"""
from pathlib import Path
import ast, copy, hashlib, importlib.util, json, re, sys

HERE = Path(__file__).resolve()
REC = HERE.parents[1]
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121'

spec = importlib.util.spec_from_file_location('ggen', HERE.parent / 'generate_n101p420_graph.py')
ggen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ggen)


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


DEF = re.compile(r'^def n(\d+) \(p : Fin 4 → ℤ\) : Expr \(Fin 9\) := (.*?)(  -- .*)?$')


def parse_poly(text):
    """An integer polynomial in `p j` as {(e0,e1,e2,e3): c}."""
    t = re.sub(r'p (\d)', r'p[\1]', text).replace('^', '**')
    def visit(e):
        if isinstance(e, ast.Expression):
            return visit(e.body)
        if isinstance(e, ast.Constant) and type(e.value) is int:
            return {(0, 0, 0, 0): e.value} if e.value else {}
        if isinstance(e, ast.Subscript):
            k = e.slice.value
            return {tuple(int(j == k) for j in range(4)): 1}
        if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub):
            return {m: -c for m, c in visit(e.operand).items()}
        if isinstance(e, ast.BinOp):
            a = visit(e.left)
            if isinstance(e.op, ast.Pow):
                out = {(0, 0, 0, 0): 1}
                for _ in range(e.right.value):
                    out = mul(out, a)
                return out
            b = visit(e.right)
            if isinstance(e.op, ast.Add):
                return add(a, b)
            if isinstance(e.op, ast.Sub):
                return add(a, {m: -c for m, c in b.items()})
            if isinstance(e.op, ast.Mult):
                return mul(a, b)
        raise SystemExit('FAIL: unparsable leaf ' + text)
    return visit(ast.parse(t, mode='eval'))


def add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            out[m] = out.get(m, 0) + ca * cb
    return {m: c for m, c in out.items() if c}


def parse_lean(text):
    nodes = {}
    for line in text.splitlines():
        m = DEF.match(line)
        if not m:
            continue
        i, body = int(m.group(1)), m.group(2).strip()
        if body.startswith('.var '):
            nodes[i] = ('variable', int(body[5:]))
        elif body == '.constant baseScale':
            nodes[i] = ('scale', 'base_scale')
        elif body == '.constant thresholdScale':
            nodes[i] = ('scale', 'threshold_scale')
        elif body.startswith('.constant ('):
            inner = body[len('.constant ('):-1]
            if re.fullmatch(r'-?\d+', inner):
                nodes[i] = ('literal', int(inner))
            else:
                nodes[i] = ('poly', parse_poly(inner))
        else:
            mm = re.fullmatch(r'n(\d+) p ([+*-]) n(\d+) p', body)
            need(mm is not None, f'unparsable node {i}')
            op = {'+': 'add', '-': 'sub', '*': 'mul'}[mm.group(2)]
            nodes[i] = (op, int(mm.group(1)), int(mm.group(3)))
    need(sorted(nodes) == list(range(len(nodes))), 'node numbering')
    return [nodes[i] for i in range(len(nodes))]


def expected(d):
    out = []
    for nd in d['nodes']:
        k = nd['kind']
        if k == 'variable':
            out.append(('variable', ggen.VARS.index(nd['name'])))
        elif k == 'literal':
            out.append(('literal', nd['value']))
        elif k == 'fixed' and nd['name'] in ('base_scale', 'threshold_scale'):
            out.append(('scale', nd['name']))
        elif k == 'fixed':
            out.append(('poly', ggen.recipe(d, nd['name'])))
        else:
            out.append((k, nd['left'], nd['right']))
    return out


def binds(parsed, exp):
    return len(parsed) == len(exp) and all(a == b for a, b in zip(parsed, exp))


def main():
    report = {}
    d = ggen.load()
    cf = ggen.analyse(d)
    layout = ggen.layout_data()
    ggen.numeric_checks(d, cf, layout)
    text = ggen.full(d, cf)
    lean_text = (LEAN / 'N101p420Graph.lean').read_text(encoding='utf-8')
    need(lean_text == text, 'stale N101p420Graph.lean')
    report['generated_file'] = 'Nine121/N101p420Graph.lean'
    report['json_sha256'] = ggen.PIN
    # 2. gate by gate
    parsed = parse_lean(lean_text)
    exp = expected(d)
    need(binds(parsed, exp), 'Lean literal differs from the JSON DAG')
    report['nodes'] = len(parsed)
    report['operations'] = sum(1 for n in parsed if n[0] in ('add', 'sub', 'mul'))
    need(report['operations'] == 420, 'operation count')
    # 3. the endpoint expression
    ep = (LEAN / 'IPRANine101p420.lean').read_text(encoding='utf-8')
    need(re.search(r'def expression : Expr \(Fin 9\) :=\n  N101p420Graph\.n451 \(fun j => '
                   r'\(Mixed121Ports\.ports j : ℤ\)\)', ep) is not None, 'endpoint expression')
    report['endpoint_expression'] = 'n451 at Mixed121Ports.ports'
    # 4. mutations
    rej = {}
    def mutated(f):
        m = copy.deepcopy(parsed)
        f(m)
        return not binds(m, exp)
    first_op = next(i for i, n in enumerate(parsed) if n[0] == 'mul')
    rej['child'] = mutated(lambda m: m.__setitem__(first_op, (m[first_op][0], m[first_op][1], m[first_op][2] - 1)))
    rej['operation'] = mutated(lambda m: m.__setitem__(first_op, ('add',) + m[first_op][1:]))
    lit = next(i for i, n in enumerate(parsed) if n[0] == 'literal')
    rej['literal'] = mutated(lambda m: m.__setitem__(lit, ('literal', m[lit][1] + 1)))
    rej['variable'] = mutated(lambda m: m.__setitem__(4, ('variable', 3)))
    poly = next(i for i, n in enumerate(parsed) if n[0] == 'poly')
    rej['coefficient_recipe'] = mutated(
        lambda m: m.__setitem__(poly, ('poly', add(m[poly][1], {(0, 0, 0, 0): 1}))))
    rej['scale'] = mutated(lambda m: m.__setitem__(9, ('scale', 'threshold_scale')))
    d2 = copy.deepcopy(d)
    five = next(i for i, n in enumerate(d2['nodes']) if n['kind'] == 'literal' and n['value'] == 5)
    d2['nodes'][five]['value'] = 6
    vals = [3, 5, 7, 11, 13, 17, 19, 23, 29]
    ports = [31, 37, 41, 43]
    ev = ggen.mod_eval(d2, vals, ports)
    mdl = ggen.model(d, vals, ports, layout)
    rej['json_literal_changes_output'] = ev[451] != mdl['value']
    need(all(rej.values()), 'a mutation was accepted')
    report['rejected_mutations'] = rej
    report['status'] = 'PASS'
    (REC / 'CHECK_GRAPH.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n',
                                          encoding='utf-8')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
