#!/usr/bin/env python3
"""Binding checker for the Nine121 Lean modules of the 101/420 nine-positive campaign.

Checks (exact integer polynomial arithmetic, standard library only):
  1. the generated Lean files N101Source.lean and N101Layout.lean are byte-identical to a fresh
     run of generate_n101_layout.py (which itself re-derives every row, the affine map, the
     22 target sets and the extraction identity from the pinned JSON);
  2. Source31Rows.rows is a verbatim copy of SplitCertificate59.sourceRows, and both parse to the
     22 parent equations of parent_source.json (SHA-256 pinned);
  3. the four original31 ports of package 101 have the SHA-256 of package 55's
     wang943-mixed-121x8801 payloads (the tuple of Mixed121Ports.ports);
  4. rejected mutations: a changed kernel coefficient, a changed weight, a changed target, a
     changed parent-row coefficient and a changed port hash are each detected.
Writes CHECK.json next to the record README.
"""
from pathlib import Path
import ast, copy, hashlib, importlib.util, json, re, sys

HERE = Path(__file__).resolve()
REC = HERE.parents[1]
DC = HERE.parents[3]
LEAN = DC / 'Lean/DiophantineConsistency'
FORMS = DC / 'con-zfc-diophantine-forms'


def need(ok, msg):
    if not ok:
        raise SystemExit('FAIL: ' + msg)


spec = importlib.util.spec_from_file_location('gen', HERE.parent / 'generate_n101_layout.py')
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)


def lean_rows(path, name):
    src = path.read_text(encoding='utf-8')
    m = re.search(r'def ' + name + r' \(ports : Fin 4 → R\) \(x : Fin 31 → R\) : Fin 22 → R :=\n  !\[(.*?)\]\n', src, re.S)
    need(m is not None, 'rows block in ' + path.name)
    return [r.strip() for r in m.group(1).split(',\n')]


def parse_row(text, n=35):
    t = re.sub(r'x (\d+)', r'x[\1]', text)
    t = re.sub(r'ports (\d+)', r'p[\1]', t).replace('^', '**')
    def visit(e):
        if isinstance(e, ast.Expression):
            return visit(e.body)
        if isinstance(e, ast.Constant) and type(e.value) is int:
            return {(0,) * n: e.value} if e.value else {}
        if isinstance(e, ast.Subscript):
            base = e.value.id
            idx = e.slice.value
            k = idx if base == 'x' else 31 + idx
            return gen.var(k, n)
        if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub):
            return {m: -c for m, c in visit(e.operand).items()}
        if isinstance(e, ast.BinOp):
            a, b = visit(e.left), None
            if isinstance(e.op, ast.Pow):
                need(isinstance(e.right, ast.Constant), 'power exponent')
                return gen.power(a, e.right.value, n)
            b = visit(e.right)
            if isinstance(e.op, ast.Add):
                return gen.add(a, b)
            if isinstance(e.op, ast.Sub):
                return gen.add(a, b, -1)
            if isinstance(e.op, ast.Mult):
                return gen.mul(a, b)
        raise SystemExit('FAIL: unparsable row term')
    return visit(ast.parse(t, mode='eval'))


def extraction_ok(d):
    """Recompute the 22 extraction identities from (possibly mutated) data."""
    w, E, pos, coef, rows = d['w'], d['E'], d['pos'], d['coef'], d['rows']
    n = 35
    def lift(pp):
        return {(0,) * 31 + m: c for m, c in pp.items()}
    for k in range(22):
        total = {}
        for i in range(31):
            for j in range(31):
                for p in range(len(pos[2])):
                    if w[i] + w[j] + pos[2][p] == E[k]:
                        total = gen.add(total, gen.mul(gen.mul(gen.var(i, n), gen.var(j, n)), lift(coef[2][p])))
            for p in range(len(pos[1])):
                if w[i] + pos[1][p] == E[k]:
                    total = gen.add(total, gen.mul(gen.var(i, n), lift(coef[1][p])))
        for p in range(len(pos[0])):
            if pos[0][p] == E[k]:
                total = gen.add(total, lift(coef[0][p]))
        if total != {m: 2 * c for m, c in rows[k].items()}:
            return False
    return True


def main():
    report = {}
    # 1. generated files
    d = gen.analyse()
    out = gen.render(d)
    for name, text in out.items():
        need((LEAN / 'Nine121' / name).read_text(encoding='utf-8') == text, 'stale generated ' + name)
    report['generated_files'] = sorted(out)
    report['interactions'] = [sum(map(len, d[s])) for s in ('S2', 'S1', 'S0')]
    report['kernel_records'] = list(d['counts'])
    # 2. parent rows
    ours = lean_rows(LEAN / 'Nine121/Source31Rows.lean', 'rows')
    theirs = lean_rows(LEAN / 'SplitCertificate59.lean', 'sourceRows')
    need(ours == theirs, 'Source31Rows differs from SplitCertificate59.sourceRows')
    docs, _ = gen.load()
    parent = docs['parent']
    names = parent['variables'] + parent['constants']
    porder = parent['sparse_term_coordinate_order']
    pj = [gen.poly_of(eq, porder, names) for eq in parent['equations']]
    for k, text in enumerate(ours):
        need(parse_row(text) == pj[k], f'parent row {k}')
    report['parent_rows'] = 22
    # 3. ports
    p55 = json.loads((FORMS / '55-congruence-norms/fourteen/coefficients/ports.json').read_text())
    need(p55['instance'] == 'wang943-mixed-121x8801', '55 instance')
    rec = json.loads((FORMS / '101-constructive-reductions/nine/COEFFICIENT_RECONSTRUCTION.json').read_text())
    h55 = [p['sha256'] for p in p55['ports']]
    h101 = [p['sha256'] for p in rec['original31']]
    need(h55 == h101 and all(p['equal'] for p in rec['original31']), 'port payload hashes')
    report['ports_sha256'] = dict(zip(['beta', 'K', 'MC', 'MF'], h55))
    # 4. mutations
    need(extraction_ok(d), 'unmutated extraction')
    rejected = {}
    m1 = copy.deepcopy(d); m1['coef'][2][5] = gen.add(m1['coef'][2][5], {(0, 0, 0, 0): 1})
    rejected['kernel_coefficient'] = not extraction_ok(m1)
    m2 = copy.deepcopy(d); m2['w'][7] += 1
    rejected['weight'] = not extraction_ok(m2)
    m3 = copy.deepcopy(d); m3['E'][4] += 1
    rejected['target'] = not extraction_ok(m3)
    m4 = list(ours); m4[9] = m4[9].replace('(-3)', '(-4)', 1)
    rejected['parent_row'] = parse_row(m4[9]) != pj[9]
    m5 = list(h101); m5[1] = m5[1][:-1] + ('0' if m5[1][-1] != '0' else '1')
    rejected['port_hash'] = m5 != h55
    need(all(rejected.values()), 'a mutation was accepted')
    report['rejected_mutations'] = rejected
    report['pins'] = d['pins']
    report['status'] = 'PASS'
    (REC / 'CHECK.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
