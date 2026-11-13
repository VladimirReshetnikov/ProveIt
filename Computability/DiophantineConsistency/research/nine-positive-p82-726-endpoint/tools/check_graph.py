#!/usr/bin/env python3
"""Binding checker for the Lean literal of package 82's 726-operation laurent9_positive equation.

Checks (standard library only):
  1. Nine121/N82p726Graph.lean is byte-identical to a fresh run of generate_n82p726_graph.py, whose
     own numeric gate (exact arithmetic modulo 2^127 - 1 at random points) verifies every closed form,
     every register formula and output = N82Finalizer.value(prefix) on the JSON DAG (with T evaluated
     independently as 4 T0 from the 654-term laurent_candidate.json);
  2. gate by gate, independently of the generator: every `def n<i>` of the Lean file is parsed back
     (variable index, integer literal, scale leaf, port polynomial of a coefficient leaf, or operation
     with its two children) and compared with node i of the pinned JSON (SHA-256 pinned);
  3. IPRANine82p726.expression is node 860 at Mixed121Ports.ports, and the majorant block
     `N82Majorant.tBlock` (whose ring instance `TR` is the value of node 844 by `r844`) is parsed back
     let by let and compared with the JSON cone of node 844 above A (389), C (4), i (426), t (439);
     N82Majorant.lean is byte-identical to a fresh run of generate_n82_majorant.py (which re-proves the
     three identities as exact polynomial identities and checks the package's cone certificate);
  4. rejected mutations: a changed child, operation, literal, variable, coefficient recipe and scale
     in the parsed literal are each detected; a changed JSON literal and a changed literal of the
     majorant cone change the output modulo the prime; a changed block literal or operation is
     detected by the block comparison.
Writes CHECK_GRAPH.json next to the record README.
"""
from pathlib import Path
import ast, copy, importlib.util, json, re

HERE = Path(__file__).resolve()
REC = HERE.parents[1]
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency/Nine121'


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ggen = load_module('ggen82', HERE.parent / 'generate_n82p726_graph.py')
mgen = load_module('mgen82', HERE.parent / 'generate_n82_majorant.py')


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


DEF = re.compile(r'^def n(\d+) \(p : Fin 4 → ℤ\) : Expr \(Fin 9\) := (.*?)(  -- .*)?$')


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


def parse_poly(text):
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
        elif body == '.constant thresholdScale82':
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


BLOCK = re.compile(r'^  let x(\d+) := (?:lit \((-?\d+)\)|(add|sub|mul) (\w+) (\w+))$')
LEAF = {'a': 389, 'c': 4, 'i': 426, 't': 439}


def parse_block(text):
    body = text[text.index('def tBlock'):text.index('/-- `T` in a commutative ring. -/')]
    out = {}
    for line in body.splitlines():
        m = BLOCK.match(line)
        if not m:
            continue
        k = int(m.group(1))
        need(k not in out, f'duplicate block let {k}')
        if m.group(2) is not None:
            out[k] = ('literal', int(m.group(2)))
        else:
            ref = lambda t: LEAF[t] if t in LEAF else int(t[1:])
            out[k] = (m.group(3), ref(m.group(4)), ref(m.group(5)))
    need('\n  x844\n' in body, 'block result is x844')
    return out


def expected_block(d):
    out = {}
    seen, st = set(), [844]
    while st:
        k = st.pop()
        if k in seen or k in LEAF.values():
            continue
        seen.add(k)
        nd = d['nodes'][k]
        if nd['kind'] == 'literal':
            out[k] = ('literal', nd['value'])
        else:
            out[k] = (nd['kind'], nd['left'], nd['right'])
            st += [nd['left'], nd['right']]
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
    lean_text = (LEAN / 'N82p726Graph.lean').read_text(encoding='utf-8')
    need(lean_text == text, 'stale N82p726Graph.lean')
    report['generated_file'] = 'Nine121/N82p726Graph.lean'
    report['json_sha256'] = ggen.PIN
    # 2. gate by gate
    parsed = parse_lean(lean_text)
    exp = expected(d)
    need(binds(parsed, exp), 'Lean literal differs from the JSON DAG')
    report['nodes'] = len(parsed)
    report['operations'] = sum(1 for n in parsed if n[0] in ('add', 'sub', 'mul'))
    report['operation_kinds'] = {k: sum(1 for n in parsed if n[0] == k) for k in ('add', 'sub', 'mul')}
    need(report['operations'] == 726, 'operation count')
    # 3. the endpoint expression, the majorant block, the majorant module
    ep = (LEAN / 'IPRANine82p726.lean').read_text(encoding='utf-8')
    need(re.search(r'def expression : Expr \(Fin 9\) :=\n  N82p726Graph\.n860 \(fun j => '
                   r'\(Mixed121Ports\.ports j : ℤ\)\)', ep) is not None, 'endpoint expression')
    report['endpoint_expression'] = 'n860 at Mixed121Ports.ports'
    maj = (LEAN / 'N82Majorant.lean').read_text(encoding='utf-8')
    md = mgen.analyse()
    need(maj == mgen.render(md), 'stale N82Majorant.lean')
    blk = parse_block(maj)
    eblk = expected_block(d)
    need(blk == eblk, 'N82Majorant.tBlock differs from the JSON cone of node 844')
    need('theorem r844 : (n844 p).evalRing w = N82Majorant.TR ((n389 p).evalRing w) (w 5) (w 6) '
         '((n439 p).evalRing w) := by' in lean_text, 'r844 statement')
    report['majorant_block'] = f'tBlock = JSON cone of node 844 ({len(blk)} lets) above A, C, i, t'
    report['majorant_module'] = {k: md['stats'][k] for k in ('T0_terms', 'defect_terms', 'top_group', 'rest_terms',
                                                             'kappa', 'nu_bits', 'kron', 'cone_terms')}
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
    rej['scale'] = mutated(lambda m: m.__setitem__(11, ('scale', 'threshold_scale')))
    vals = [3, 5, 7, 11, 13, 17, 19, 23, 29]
    ports = [31, 37, 41, 43]
    mdl = ggen.model(vals, ports, layout)
    need(ggen.mod_eval(d, vals, ports)[860] == mdl['value'], 'unmutated output at the test point')
    d2 = copy.deepcopy(d)
    d2['nodes'][392]['value'] += 1          # the literal 5 of J = 4A - 5
    rej['json_literal_changes_output'] = ggen.mod_eval(d2, vals, ports)[860] != mdl['value']
    d3 = copy.deepcopy(d)
    d3['nodes'][511]['value'] += 1          # a literal of the correction block
    rej['json_majorant_literal_changes_output'] = ggen.mod_eval(d3, vals, ports)[860] != mdl['value']
    k0 = min(k for k, v in blk.items() if v[0] == 'literal')
    b2 = dict(blk); b2[k0] = ('literal', b2[k0][1] + 1)
    rej['majorant_block_literal'] = b2 != eblk
    k1 = min(k for k, v in blk.items() if v[0] == 'mul')
    b3 = dict(blk); b3[k1] = ('add',) + b3[k1][1:]
    rej['majorant_block_operation'] = b3 != eblk
    need(all(rej.values()), 'a mutation was accepted')
    report['rejected_mutations'] = rej
    report['status'] = 'PASS'
    (REC / 'CHECK_GRAPH.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n',
                                          encoding='utf-8')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
