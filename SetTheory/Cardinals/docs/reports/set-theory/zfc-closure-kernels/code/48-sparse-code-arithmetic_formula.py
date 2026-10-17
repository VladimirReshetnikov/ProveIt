#!/usr/bin/env python3
"""Emit explicit finite arithmetic graphs for the exact C254 checker.

The output uses only bounded-quantifier abbreviations and finite circuits.
Every displayed macro has a definition; expansion gives first-order formulas
over natural-number addition, multiplication, order and equality. This is a
formula artifact, not a Lean/PA kernel proof.
"""
from pathlib import Path
import json
from sparse_c254 import DATA


class Circuit:
    def __init__(self, definitions):
        self.definitions = definitions
        self.gates = []
        self.shared = {}

    def term(self, tree, env):
        if isinstance(tree, int):
            return str(tree)
        if isinstance(tree, str):
            return env[tree]
        return self.call(tree[0], [self.term(a, env) for a in tree[1:]])

    def call(self, name, args):
        if name in ('wim', 'wel', 'wal', 'weq'):
            key = tuple(args)
            if key not in self.shared:
                g = f'g{len(self.gates)}'
                self.shared[key] = g
                self.gates.append((g, *args))
            g = self.shared[key]
            offset = ('wim', 'wel', 'wal', 'weq').index(name)
            return f'(4*{g}' + (f'+{offset}' if offset else '') + ')'
        entry = self.definitions[name]
        return self.term(entry['tree'], dict(zip(entry['params'], args)))

    def formula(self, name):
        params = ['a', 'b'] if name in ('wim', 'wel', 'wal', 'weq') else self.definitions[name]['params']
        output = self.call(name, params)
        quantified = ','.join(g for g, _, _ in self.gates)
        clauses = [f'PAIR({g},{a},{b})' for g, a, b in self.gates] + [f'o={output}']
        return f'GRAPH_{name}(' + ','.join(params + ['o', 'W']) + ') :=\n' + \
            f'  EXISTS {quantified} <= W (\n    ' + '\n    AND '.join(clauses) + '\n  ).\n'


def row_formula(kind):
    if kind == 'D':
        args = 'k,v,B,C,W'
        lookup = lambda child, value: f'BETA(B,C,{child},{value})'
    else:
        args = 'i,k,v,Bk,Ck,Bv,Cv,W'
        lookup = lambda child, value: f'LOOKUP(i,{child},{value},Bk,Ck,Bv,Cv,W)'
    mp = (f'EXISTS x,y <= W ({lookup("b", "x")} AND {lookup("d", "y")} AND\n'
          '      (((x=0 OR y=0) AND v=0) OR\n'
          '       EXISTS xp,yp,z <= W (x=xp+1 AND y=yp+1 AND GRAPH_wim(xp,a,z,W) AND\n'
          '          ((yp=z AND v=a+1) OR (yp!=z AND v=0)))))')
    gen = (f'EXISTS x <= W ({lookup("t", "x")} AND\n'
           '      ((x=0 AND v=0) OR EXISTS xp,n <= W\n'
           '        (x=xp+1 AND GRAPH_wal(a,xp,n,W) AND v=n+1)))')
    branches = [
        '(tag=0 AND ((p=0 AND v=1) OR (p!=0 AND v=0)))',
        '(tag=1 AND b<k AND d<k AND ' + mp + ')',
        '(tag=2 AND t<k AND ' + gen + ')',
    ]
    parameters = {3: ('rho1', 'a,t'), 4: ('rho2', 'a,b,d'),
                  5: ('rho3', 'a,b,d'), 6: ('rho4', 'a,b,d'),
                  7: ('rho5', 'a,b,d'), 8: ('rho6', 'a,t'),
                  9: ('rho7', 'a,b,d'), 10: ('rho8', 'a,b,e,f')}
    for tag, (name, ps) in parameters.items():
        branches.append(f'(tag={tag} AND EXISTS n <= W (GRAPH_{name}({ps},n,W) AND v=n+1))')
    branches.append('(tag=11 AND (((d=a OR d=b) AND v=0) OR\n'
                    '      (d!=a AND d!=b AND EXISTS n <= W (GRAPH_bundle(a,b,d,n,W) AND v=n+1))))')
    return f'ROW_{kind}({args}) :=\n  (k=0 AND v=0) OR\n' + \
        '  EXISTS tag,p,a,t,b,d,e,f <= W (\n' + \
        '    k>0 AND tag<12 AND k=12*p+tag+1 AND\n' + \
        '    PAIR(p,a,t) AND PAIR(t,b,d) AND PAIR(d,e,f) AND (\n    ' + \
        '\n    OR '.join(branches) + '\n    )\n  ).\n'


def main():
    definitions = json.loads((DATA / 'formula_circuits.json').read_text())['definitions']
    header = '''EXACT C254 ARITHMETIC GRAPHS

All variables range over the natural numbers. EXISTS x,y <= W abbreviates
EXISTS x (x<=W AND EXISTS y (y<=W AND ...)); FORALL i<m has the usual bounded
meaning. Every macro below is a finite textual abbreviation. On expansion,
alpha-rename every bound variable to a fresh name to avoid variable capture.
There are no uninterpreted recursive functions in the expanded formulas.

PAIR(z,x,y) := 2*z=(x+y)*(x+y+1)+2*y.

BETA(B,C,i,v) :=
  v < 1+(i+1)*C AND
  EXISTS q<=B (B=q*(1+(i+1)*C)+v).

LOOKUP(i,k,v,Bk,Ck,Bv,Cv,W) :=
  EXISTS j<i (BETA(Bk,Ck,j,k) AND BETA(Bv,Cv,j,v)).

'''
    circuits = []
    metrics = {}
    for name in ['wim', 'wal'] + [f'rho{i}' for i in range(1, 9)] + ['bundle']:
        circuit = Circuit(definitions)
        circuits.append(circuit.formula(name))
        metrics[name] = len(circuit.gates)
    footer = '''
CHECK_DENSE(c,n) :=
  EXISTS B,C,W (
    C>=1 AND c<=W AND n+1<=W AND BETA(B,C,c,n+1) AND
    FORALL i<=c EXISTS v<=W
      (BETA(B,C,i,v) AND ROW_D(i,v,B,C,W))
  ).

CHECK_SPARSE(c,n) :=
  EXISTS m,last,Bk,Ck,Bv,Cv,W (
    m=last+1 AND m<=W AND Ck>=1 AND Cv>=1 AND c<=W AND n+1<=W AND
    BETA(Bk,Ck,0,0) AND BETA(Bv,Cv,0,0) AND
    BETA(Bk,Ck,last,c) AND BETA(Bv,Cv,last,n+1) AND
    FORALL i<m EXISTS k,v<=W (
      BETA(Bk,Ck,i,k) AND BETA(Bv,Cv,i,v) AND k<=c AND
      (FORALL j<i FORALL h<=W (BETA(Bk,Ck,j,h) IMPLIES h<k)) AND
      ROW_S(i,k,v,Bk,Ck,Bv,Cv,W)
    )
  ).

REJECT_SPARSE(c,n) :=
  EXISTS m,last,Bk,Ck,Bv,Cv,W,r (
    m=last+1 AND m<=W AND Ck>=1 AND Cv>=1 AND c<=W AND r<=W AND
    BETA(Bk,Ck,0,0) AND BETA(Bv,Cv,0,0) AND
    BETA(Bk,Ck,last,c) AND BETA(Bv,Cv,last,r) AND r!=n+1 AND
    FORALL i<m EXISTS k,v<=W (
      BETA(Bk,Ck,i,k) AND BETA(Bv,Cv,i,v) AND k<=c AND
      (FORALL j<i FORALL h<=W (BETA(Bk,Ck,j,h) IMPLIES h<k)) AND
      ROW_S(i,k,v,Bk,Ck,Bv,Cv,W)
    )
  ).

Both CHECK formulas and REJECT_SPARSE are Sigma_1 after expanding the finite
graphs and bounded quantifiers. Total existence and uniqueness of the
evaluated value are proved in the accompanying report. Consequently
REJECT_SPARSE(c,n) is equivalent to NOT CHECK_SPARSE(c,n).

The bound W is existential certificate data, not a fixed resource cutoff.
It bounds every evaluated value and circuit gate in that certificate.
Missing sparse children fail LOOKUP; they are never silently treated as valid.
The designated proof code 0 is explicitly represented by the initial invalid
row (0,0). Formula code 0 remains truth; a proof of it has stored value 1.
'''
    output = header + '\n'.join(circuits) + '\n' + row_formula('D') + '\n' + row_formula('S') + footer
    (DATA / 'arithmetic_graphs.txt').write_text(output)
    record = {'pair_gates_by_graph': metrics, 'formula_bytes': len(output.encode()),
              'total_graph_pair_gates': sum(metrics.values()),
              'scope': 'Explicit first-order arithmetic formulas with bounded abbreviations; no new kernel-checked PA theorem.'}
    (DATA / 'arithmetic_graph_metrics.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
