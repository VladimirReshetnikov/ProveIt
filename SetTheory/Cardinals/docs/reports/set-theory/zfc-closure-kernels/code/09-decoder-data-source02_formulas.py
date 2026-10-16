"""Formula templates for the closure-kernel comparison.

Standard library only. These are syntax/measurement tools, not a proof checker.
Variables and schema-hole arguments are payloads, not formula nodes. Derived
connectives are expanded into ->, forall and bottom for the reported metric.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable

@dataclass(frozen=True)
class Formula:
    op: str
    args: tuple

    def __post_init__(self) -> None:
        arities = {'in': 2, 'eq': 2, 'hole': 3, 'bot': 0, 'imp': 2,
                   'and': 2, 'or': 2, 'iff': 2, 'not': 1,
                   'all': 2, 'ex': 2}
        if self.op not in arities or len(self.args) != arities[self.op]:
            raise ValueError(f'Invalid formula constructor: {self.op!r}')


def In(x: str, y: str) -> Formula: return Formula('in', (x, y))
def Eq(x: str, y: str) -> Formula: return Formula('eq', (x, y))
def Hole(x: str, y: str = '', label: str = 'R') -> Formula:
    return Formula('hole', (x, y, label))
def Bot() -> Formula: return Formula('bot', ())
def Imp(a: Formula, b: Formula) -> Formula: return Formula('imp', (a, b))
def And(a: Formula, b: Formula) -> Formula: return Formula('and', (a, b))
def Or(a: Formula, b: Formula) -> Formula: return Formula('or', (a, b))
def Iff(a: Formula, b: Formula) -> Formula: return Formula('iff', (a, b))
def Not(a: Formula) -> Formula: return Formula('not', (a,))
def All(x: str, a: Formula) -> Formula: return Formula('all', (x, a))
def Ex(x: str, a: Formula) -> Formula: return Formula('ex', (x, a))
def alls(xs: Iterable[str], a: Formula) -> Formula:
    for x in reversed(tuple(xs)): a = All(x, a)
    return a

def Sub(x: str, y: str, z: str = 'z') -> Formula:
    return All(z, Imp(In(z, x), In(z, y)))

def expand(f: Formula) -> Formula:
    """Classically equivalent expansion; each occurrence is counted separately."""
    o, a = f.op, f.args
    if o in {'in', 'eq', 'hole', 'bot'}: return f
    if o == 'not': return Imp(expand(a[0]), Bot())
    if o == 'and':
        p, q = map(expand, a)
        return Imp(Imp(p, Imp(q, Bot())), Bot())
    if o == 'or': return Imp(Imp(expand(a[0]), Bot()), expand(a[1]))
    if o == 'iff': return expand(And(Imp(a[0], a[1]), Imp(a[1], a[0])))
    if o == 'ex': return Imp(All(a[0], Imp(expand(a[1]), Bot())), Bot())
    if o == 'all': return All(a[0], expand(a[1]))
    return Imp(expand(a[0]), expand(a[1]))

def count(f: Formula) -> dict[str, int]:
    out: dict[str, int] = {}
    def walk(g: Formula) -> None:
        out[g.op] = out.get(g.op, 0) + 1
        if g.op in {'all', 'ex'}: walk(g.args[1])
        elif g.op == 'not': walk(g.args[0])
        elif g.op in {'imp', 'and', 'or', 'iff'}:
            walk(g.args[0]); walk(g.args[1])
    walk(f)
    return out

def text(f: Formula) -> str:
    o, a = f.op, f.args
    if o == 'in': return f'({a[0]} in {a[1]})'
    if o == 'eq': return f'({a[0]} = {a[1]})'
    if o == 'hole': return f'{a[2]}({a[0]}' + (f',{a[1]}' if a[1] else '') + ')'
    if o == 'bot': return 'FALSE'
    if o in {'all', 'ex'}: return f'({o} {a[0]}. {text(a[1])})'
    if o == 'not': return f'(not {text(a[0])})'
    return f'({text(a[0])} {o} {text(a[1])})'


def templates() -> dict[str, Formula]:
    e = alls(['x', 'y'], Imp(All('z', Iff(In('z', 'x'), In('z', 'y'))), Eq('x', 'y')))
    ec = alls(['x', 'y'], Imp(All('z', Iff(In('z', 'x'), In('z', 'y'))),
                            All('w', Iff(In('x', 'w'), In('y', 'w')))))
    ne = Ex('a', Ex('b', In('a', 'b')))
    sep = All('A', Ex('C', All('y', Iff(In('y', 'C'), And(In('y', 'A'), Hole('y', label='P'))))))
    power = All('A', Ex('C', All('y', Iff(In('y', 'C'), Sub('y', 'A')))))
    local_sub = All('x', Ex('b', All('y', Imp(Hole('x', 'y'), Sub('y', 'b')))))
    local_mem = All('x', Ex('b', All('y', Imp(Hole('x', 'y'), In('y', 'b')))))
    closed = alls(['x', 'y'], Imp(And(In('x', 'W'), Hole('x', 'y')), In('y', 'W')))
    root = All('a', Ex('W', And(In('a', 'W'), closed)))
    tc = Imp(local_mem, root)
    sbc = Imp(local_sub, root)
    tcset = Imp(local_mem, All('A', Ex('W', And(Sub('A', 'W'), closed))))
    sbi_premise = All('x', Imp(In('x', 'A'), Ex('b', All('y', Imp(Hole('x', 'y'), Sub('y', 'b'))))))
    sbi = All('A', Imp(sbi_premise, Ex('C', All('y', Iff(In('y', 'C'),
                        Ex('x', And(In('x', 'A'), Hole('x', 'y'))))))))
    closure = alls(['x', 'y'], Imp(And(Or(In('x', 'A'), In('x', 'C')), Hole('x', 'y')), In('y', 'C')))
    support = All('y', Imp(In('y', 'C'), Ex('x', Hole('x', 'y'))))
    isi = Imp(local_sub, All('A', Ex('C', And(closure, support))))
    local_mix = All('x', Ex('b', All('y', Imp(Hole('x', 'y'), Or(In('y', 'b'), Sub('y', 'b'))))))
    point_closure = alls(['x', 'y'], Imp(And(Or(Eq('x', 'a'), In('x', 'C')), Hole('x', 'y')), In('y', 'C')))
    pibi = Imp(local_mix, All('a', Ex('C', And(point_closure, support))))
    pisi = Imp(local_sub, All('a', Ex('C', And(point_closure, support))))
    subset_closure = alls(['x', 'y'], Imp(And(Or(Sub('x', 'a'), In('x', 'C')), Hole('x', 'y')), In('y', 'C')))
    sibi = Imp(local_mix, All('a', Ex('C', And(subset_closure, support))))
    empty = Ex('e', And(All('z', Not(In('z', 'e'))), In('e', 'I')))
    succ = All('x', Imp(In('x', 'I'), Ex('s', And(In('s', 'I'),
                 All('z', Iff(In('z', 's'), Or(In('z', 'x'), Eq('z', 'x'))))))))
    inf = Ex('I', And(empty, succ))
    cp = All('p', Ex('V', And(In('p', 'V'), All('x', Imp(In('x', 'V'),
         And(Sub('x', 'V'), Ex('W', And(In('W', 'V'), All('z', Imp(Sub('z', 'x', 'u'), In('z', 'W')))))))))))
    gic = All('B', Ex('C', And(All('x', Imp(In('x', 'B'), All('y', Imp(Hole('x', 'y'),
           Ex('v', And(Hole('x', 'v'), In('v', 'C'))))))), support)))
    return {'Ext': e, 'EC': ec, 'NE': ne, 'Sep': sep, 'Power': power,
            'TC_root': tc, 'TC_set': tcset, 'SBC': sbc, 'SBI': sbi,
            'ISI': isi, 'PIBI': pibi, 'SIBI': sibi, 'PISI_open': pisi, 'Infinity': inf, 'CP': cp, 'GIC': gic}


THEORIES = {
    'MO_root': ['Ext', 'Sep', 'Power', 'TC_root'],
    'MO_set_seed': ['Ext', 'Sep', 'Power', 'TC_set'],
    'SBC': ['Ext', 'Sep', 'SBC'],
    'prior_SBI': ['Ext', 'Infinity', 'SBI'],
    'ISI': ['Ext', 'NE', 'ISI'],
    'QISI': ['EC', 'NE', 'ISI'],
    'PIBI': ['Ext', 'PIBI'],
    'SIBI': ['Ext', 'SIBI'],
    'QSIBI': ['EC', 'SIBI'],
    'RCC': ['CP', 'GIC'],
}

if __name__ == '__main__':
    import json
    from pathlib import Path
    root = Path(__file__).resolve().parents[1]
    ts = templates()
    data = {'metric': 'Formula-tree nodes in {in,eq,bottom,imp,forall}; a schema hole counts as one atom per occurrence. Variable payload costs and parameter closure are excluded.',
            'axioms': {}, 'theories': {}}
    for name, f in ts.items():
        co = count(expand(f))
        data['axioms'][name] = {'nodes': sum(co.values()), 'constructors': co}
    for name, axioms in THEORIES.items():
        data['theories'][name] = {'templates': axioms,
            'nodes': sum(data['axioms'][x]['nodes'] for x in axioms),
            'hole_occurrences': sum(data['axioms'][x]['constructors'].get('hole', 0) for x in axioms)}
    (root / 'results' / 'metrics.json').write_text(json.dumps(data, indent=2) + '\n')
    (root / 'results' / 'templates.txt').write_text('\n\n'.join(f'{k}\n{text(v)}\nExpanded:\n{text(expand(v))}' for k,v in ts.items())+'\n')
    print(json.dumps(data['theories'], indent=2))
