#!/usr/bin/env python3
"""Theory-template and concrete-formula encodings, never TM state counts.

Credits: intake sources 01--03, in the zfc-closure-kernels report. This
self-contained experiment does not modify or execute delivered code. Run this
file to write results/kernel_metrics.json; run test_kernel_metrics.py for checks.
A concrete Mem(0,1) instance is an example schema instance, not an axiomatization
of the theory. No checker, proof compiler, enumerator, or machine is supplied.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Callable, Mapping


def nat(value: object) -> int:
    if type(value) is not int or value < 0:
        raise ValueError('variable labels must be nonnegative integers, not booleans')
    return value


@dataclass(frozen=True)
class Formula:
    op: str
    args: tuple

    def __post_init__(self) -> None:
        if not isinstance(self.args, tuple):
            raise ValueError('arguments must be a tuple')
        if self.op in ('mem', 'eq') and len(self.args) == 2:
            for value in self.args: nat(value)
        elif self.op == 'hole' and len(self.args) >= 2:
            for value in self.args: nat(value)
        elif self.op == 'bot' and not self.args:
            pass
        elif self.op in ('not',) and len(self.args) == 1:
            if not isinstance(self.args[0], Formula): raise ValueError('formula child required')
        elif self.op in ('imp', 'nand') and len(self.args) == 2:
            if not all(isinstance(q, Formula) for q in self.args): raise ValueError('formula children required')
        elif self.op == 'all' and len(self.args) == 2:
            nat(self.args[0])
            if not isinstance(self.args[1], Formula): raise ValueError('formula body required')
        else:
            raise ValueError(f'unknown constructor or wrong arity: {self.op}')


F = Formula

def Mem(x: int, y: int) -> F: return F('mem', (x, y))
def Eq(x: int, y: int) -> F: return F('eq', (x, y))
def Hole(x: int, y: int) -> F: return F('hole', (x, y))
def Bot() -> F: return F('bot', ())
def Not(p: F) -> F: return F('not', (p,))
def Imp(p: F, q: F) -> F: return F('imp', (p, q))
def Nand(p: F, q: F) -> F: return F('nand', (p, q))
def All(v: int, p: F) -> F: return F('all', (v, p))
def Ex(v: int, p: F) -> F: return Not(All(v, Not(p)))
def And(p: F, q: F) -> F: return Not(Imp(p, Not(q)))
def Or(p: F, q: F) -> F: return Imp(Not(p), q)
def Iff(p: F, q: F) -> F: return And(Imp(p, q), Imp(q, p))

def alls(vs: list[int], p: F) -> F:
    for v in reversed(vs): p = All(v, p)
    return p


def children(p: F) -> tuple[F, ...]:
    if p.op == 'all': return (p.args[1],)
    return tuple(q for q in p.args if isinstance(q, F))


def variables(p: F) -> set[int]:
    if p.op in ('mem', 'eq', 'hole'): return set(p.args)
    out = {p.args[0]} if p.op == 'all' else set()
    return out.union(*(variables(q) for q in children(p)))


def free_vars(p: F) -> set[int]:
    if p.op in ('mem', 'eq', 'hole'): return set(p.args)
    if p.op == 'all': return free_vars(p.args[1]) - {p.args[0]}
    return set().union(*(free_vars(q) for q in children(p)))


def substitute(p: F, replacements: Mapping[int, int]) -> F:
    """Simultaneous capture-avoiding substitution for free variable labels."""
    replacements = {nat(k): nat(v) for k, v in replacements.items() if k != v}
    if p.op in ('mem', 'eq', 'hole'):
        return F(p.op, tuple(replacements.get(v, v) for v in p.args))
    if p.op == 'all':
        binder, body = p.args
        active = {k: v for k, v in replacements.items() if k != binder and k in free_vars(body)}
        if binder in active.values():
            fresh = max(variables(body) | set(active) | set(active.values()) | {binder}) + 1
            body = substitute(body, {binder: fresh})
            binder = fresh
        return All(binder, substitute(body, active))
    return F(p.op, tuple(substitute(q, replacements) for q in children(p)))


def normalize(p: F) -> F:
    """Only classical double-negation cancellation; no other rewriting."""
    if p.op in ('mem', 'eq', 'hole', 'bot'): return p
    if p.op == 'all': return All(p.args[0], normalize(p.args[1]))
    qs = tuple(normalize(q) for q in children(p))
    if p.op == 'not' and qs[0].op == 'not': return qs[0].args[0]
    return F(p.op, qs)


def bottom_basis(p: F) -> F:
    """Source02 basis: membership/equality/hole/bottom/implication/forall."""
    if p.op in ('mem', 'eq', 'hole', 'bot'): return p
    if p.op == 'all': return All(p.args[0], bottom_basis(p.args[1]))
    if p.op == 'not': return Imp(bottom_basis(p.args[0]), Bot())
    if p.op == 'imp': return Imp(*(bottom_basis(q) for q in p.args))
    raise ValueError('bottom_basis expects the negation/implication syntax')


def alpha_key(p: F, binders: tuple[int, ...] = ()) -> tuple:
    def key(v: int) -> tuple:
        return ('bound', binders[::-1].index(v)) if v in binders else ('free', v)
    if p.op in ('mem', 'eq', 'hole'): return (p.op, *(key(v) for v in p.args))
    if p.op == 'all': return ('all', alpha_key(p.args[1], binders + (p.args[0],)))
    return (p.op, *(alpha_key(q, binders) for q in children(p)))


def alpha_reuse(p: F) -> F:
    """Reuse low binder labels according to liveness; no minimality claim."""
    def go(q: F, mapping: dict[int, int]) -> F:
        if q.op in ('mem', 'eq', 'hole'):
            return F(q.op, tuple(mapping.get(v, v) for v in q.args))
        if q.op == 'all':
            binder, body = q.args
            forbidden = {mapping.get(v, v) for v in free_vars(body) - {binder}}
            target = 0
            while target in forbidden: target += 1
            return All(target, go(body, mapping | {binder: target}))
        return F(q.op, tuple(go(c, mapping) for c in children(q)))
    return go(p, {})


def evaluate(p: F, n: int, membership: int, env: Mapping[int, int] | None = None,
             hole: Callable[[tuple[int, ...]], bool] | None = None) -> bool:
    if n < 1: raise ValueError('domains must be nonempty')
    assignment = dict(env or {})
    def go(q: F, a: dict[int, int]) -> bool:
        op, args = q.op, q.args
        if op == 'mem': return bool(membership & (1 << (a[args[0]] * n + a[args[1]])))
        if op == 'eq': return a[args[0]] == a[args[1]]
        if op == 'hole':
            if hole is None: raise ValueError('uninstantiated matrix hole')
            return bool(hole(tuple(a[v] for v in args)))
        if op == 'bot': return False
        if op == 'not': return not go(args[0], a)
        if op == 'imp': return not go(args[0], a) or go(args[1], a)
        if op == 'nand': return not (go(args[0], a) and go(args[1], a))
        if op == 'all': return all(go(args[1], a | {args[0]: v}) for v in range(n))
        raise ValueError(op)
    return go(p, assignment)


def metrics(p: F) -> dict:
    counts: Counter[str] = Counter()
    var_occurrences = binder_occurrences = 0
    def walk(q: F) -> None:
        nonlocal var_occurrences, binder_occurrences
        counts[q.op] += 1
        if q.op in ('mem', 'eq', 'hole'): var_occurrences += len(q.args)
        if q.op == 'all':
            binder_occurrences += 1
            var_occurrences += 1
        for child in children(q): walk(child)
    walk(p)
    return dict(nodes=sum(counts.values()), operators=dict(sorted(counts.items())),
                variable_occurrences_including_binders=var_occurrences,
                binder_occurrences=binder_occurrences,
                distinct_variable_labels=len(variables(p)),
                maximum_variable_label=max(variables(p), default=None),
                free_variables=sorted(free_vars(p)))


class Context:
    def __init__(self, matrix: F | None):
        self.matrix = Hole(0, 1) if matrix is None else matrix
        self.next = max(variables(self.matrix) | {0, 1}) + 1

    def fresh(self) -> int:
        v = self.next; self.next += 1
        return v

    def at(self, x: int, y: int) -> F:
        return substitute(self.matrix, {0: x, 1: y})

    def close(self, p: F) -> F:
        return alls(sorted(free_vars(p)), p)


def subset(x: int, y: int, z: int) -> F:
    if z in (x, y): raise ValueError('subset witness must be fresh')
    return All(z, Imp(Mem(z, x), Mem(z, y)))


def profile(x: int, y: int, z: int) -> F:
    if z in (x, y): raise ValueError('profile witness must be fresh')
    return All(z, Iff(Mem(z, x), Mem(z, y)))


def congruence(symmetric: bool = False) -> F:
    conclusion = Iff(Mem(0, 3), Mem(1, 3)) if symmetric else Imp(Mem(0, 3), Mem(1, 3))
    return alls([0, 1], Imp(profile(0, 1, 2), All(3, conclusion)))


def extensionality() -> F:
    return alls([0, 1], Imp(profile(0, 1, 2), Eq(0, 1)))


def cp() -> F:
    p, v, x, w, z, t = range(6)
    return All(p, Ex(v, And(Mem(p, v), All(x, Imp(Mem(x, v),
        And(subset(x, v, t), Ex(w, And(Mem(w, v),
            All(z, Imp(subset(z, x, t), Mem(z, w)))))))))))


def gic(matrix: F | None = None) -> F:
    c = Context(matrix)
    b, output, x, y, v = [c.fresh() for _ in range(5)]
    witnesses = All(x, Imp(Mem(x, b), All(y, Imp(c.at(x, y),
        Ex(v, And(c.at(x, v), Mem(v, output)))))))
    support = All(y, Imp(Mem(y, output), Ex(x, c.at(x, y))))
    return c.close(All(b, Ex(output, And(witnesses, support))))


def seeded(matrix: F | None = None, *, seed: str = 'subset', mixed: bool = False) -> F:
    if seed not in ('point', 'subset', 'member'): raise ValueError('unknown seed')
    c = Context(matrix)
    x, y, b, a, output, z = [c.fresh() for _ in range(6)]
    bound = subset(y, b, z)
    if mixed: bound = Or(Mem(y, b), bound)
    local = All(x, Ex(b, All(y, Imp(c.at(x, y), bound))))
    start = {'point': Eq(x, a), 'subset': subset(x, a, z), 'member': Mem(x, a)}[seed]
    closed = alls([x, y], Imp(And(Or(start, Mem(x, output)), c.at(x, y)), Mem(y, output)))
    support = All(y, Imp(Mem(y, output), Ex(x, c.at(x, y))))
    return c.close(Imp(local, All(a, Ex(output, And(closed, support)))))


def efh(matrix: F | None = None) -> F:
    c = Context(matrix)
    a, v, x, y, b, z = [c.fresh() for _ in range(6)]
    local = All(x, Ex(b, All(y, Imp(c.at(x, y), subset(y, b, z)))))
    exact = Ex(b, And(Mem(b, v), All(y, Iff(Mem(y, b), c.at(x, y)))))
    hull = All(a, Ex(v, And(Mem(a, v), All(x, Imp(Mem(x, v),
        And(subset(x, v, z), exact))))))
    return c.close(Imp(local, hull))


def templates(matrix: F | None = None) -> dict[str, F]:
    return {
        'Ext': extensionality(), 'CG_oneway': congruence(),
        'CG_symmetric_MiraEsharp': congruence(True), 'CP': cp(), 'GIC': gic(matrix),
        'PSC_point_subset': seeded(matrix, seed='point'),
        'PSC_point_mixed': seeded(matrix, seed='point', mixed=True),
        'PSC_subset_subset': seeded(matrix),
        'PSC_subset_mixed': seeded(matrix, mixed=True),
        'ISI_member_subset': seeded(matrix, seed='member'),
        'EFH': efh(matrix),
    }


THEORIES = {
    'Ext_PSC_point_subset': ['Ext', 'PSC_point_subset'],
    'Ext_PSC_point_mixed': ['Ext', 'PSC_point_mixed'],
    'Ext_PSC_subset_subset': ['Ext', 'PSC_subset_subset'],
    'Ext_PSC_subset_mixed': ['Ext', 'PSC_subset_mixed'],
    'QPSC_oneway': ['CG_oneway', 'PSC_subset_subset'],
    'QPSC_symmetric': ['CG_symmetric_MiraEsharp', 'PSC_subset_subset'],
    'Qmixed_oneway': ['CG_oneway', 'PSC_subset_mixed'],
    'Qmixed_symmetric': ['CG_symmetric_MiraEsharp', 'PSC_subset_mixed'],
    'RCC': ['CP', 'GIC'],
    'Ext_EFH': ['Ext', 'EFH'],
    'QEFH_oneway': ['CG_oneway', 'EFH'],
    'QEFH_symmetric': ['CG_symmetric_MiraEsharp', 'EFH'],
}


def to_nand(p: F) -> F:
    """A complete three-constructor equality-free basis, fourth with equality.

    not A = NAND(A,A); A->B = NAND(A,NAND(B,B)). No bottom alias is used.
    The encoded tree repeats subexpressions; there is no uncharged DAG sharing.
    """
    if p.op in ('mem', 'eq'): return p
    if p.op in ('hole', 'bot'): raise ValueError('concrete hole-free, bottom-free input required')
    if p.op == 'all': return All(p.args[0], to_nand(p.args[1]))
    if p.op == 'nand': return Nand(*(to_nand(q) for q in p.args))
    if p.op == 'not':
        q = to_nand(p.args[0]); return Nand(q, q)
    if p.op == 'imp':
        a, b = (to_nand(q) for q in p.args); return Nand(a, Nand(b, b))
    raise ValueError(p.op)


def rpn(p: F) -> list[list]:
    if p.op in ('mem', 'eq'): return [[p.op, *p.args]]
    if p.op == 'all': return rpn(p.args[1]) + [['all', p.args[0]]]
    if p.op == 'nand': return rpn(p.args[0]) + rpn(p.args[1]) + [['nand']]
    raise ValueError('RPN accepts only membership/equality/NAND/forall')


def from_rpn(tokens: object) -> F:
    if not isinstance(tokens, list): raise ValueError('token list required')
    stack: list[F] = []
    for token in tokens:
        if not isinstance(token, list) or not token: raise ValueError('bad RPN token')
        op = token[0]
        if op in ('mem', 'eq') and len(token) == 3:
            stack.append(F(op, (nat(token[1]), nat(token[2]))))
        elif op == 'all' and len(token) == 2 and stack:
            stack.append(All(nat(token[1]), stack.pop()))
        elif op == 'nand' and len(token) == 1 and len(stack) >= 2:
            right, left = stack.pop(), stack.pop(); stack.append(Nand(left, right))
        else: raise ValueError('wrong arity, unsupported constructor, or RPN stack underflow')
    if len(stack) != 1: raise ValueError('RPN must have exactly one result')
    return stack[0]


def gamma(value: int) -> str:
    if type(value) is not int or value <= 0: raise ValueError('gamma codes positive integers')
    body = bin(value)[2:]
    return '0' * (len(body) - 1) + body


def serialize(p: F) -> str:
    """Frame = equality-mode bit + gamma(payload_bits+1) + RPN token payload.

    Mode0: mem=0,NAND=10,all=11. Mode1: mem=00,eq=01,NAND=10,all=11.
    Every variable occurrence, including each binder, has gamma(label+1).
    """
    tokens = rpn(p)
    equality = any(t[0] == 'eq' for t in tokens)
    codes = {'mem': '00' if equality else '0', 'eq': '01', 'nand': '10', 'all': '11'}
    payload = ''.join(codes[t[0]] + ''.join(gamma(v + 1) for v in t[1:]) for t in tokens)
    return str(int(equality)) + gamma(len(payload) + 1) + payload


def deserialize(bits: object) -> F:
    if not isinstance(bits, str) or not bits or set(bits) - {'0', '1'}:
        raise ValueError('nonempty binary string required')
    pos = 1
    def read_gamma(limit: int) -> int:
        nonlocal pos
        start = pos
        while pos < limit and bits[pos] == '0': pos += 1
        if pos >= limit: raise ValueError('truncated gamma prefix')
        zeros = pos - start
        if pos + zeros >= limit: raise ValueError('truncated gamma body')
        value = int(bits[pos:pos + zeros + 1], 2)
        pos += zeros + 1
        return value
    size = read_gamma(len(bits)) - 1
    end = pos + size
    if end != len(bits): raise ValueError('truncated payload or trailing bits')
    equality = bits[0] == '1'
    tokens = []
    while pos < end:
        if not equality and bits[pos] == '0': op = 'mem'; pos += 1
        else:
            code = bits[pos:pos + 2]
            if len(code) != 2: raise ValueError('truncated opcode')
            pos += 2
            op = {'00': 'mem', '01': 'eq', '10': 'nand', '11': 'all'}.get(code)
            if not equality and op in ('mem', 'eq'): raise ValueError('invalid mode0 opcode')
        arity = {'mem': 2, 'eq': 2, 'all': 1, 'nand': 0}[op]
        tokens.append([op, *(read_gamma(end) - 1 for _ in range(arity))])
    result = from_rpn(tokens)
    if equality != any(token[0] == 'eq' for token in tokens):
        raise ValueError('noncanonical equality mode')
    return result


def encoding_metrics(p: F, *, include_encoding: bool = False) -> dict:
    nand = to_nand(p)
    tokens = rpn(nand)
    bits = serialize(nand)
    equality = any(t[0] == 'eq' for t in tokens)
    payload_bits = sum(len(gamma(v + 1)) for t in tokens for v in t[1:])
    opcode_bits = sum(1 if t[0] == 'mem' and not equality else 2 for t in tokens)
    out = metrics(nand) | dict(basis_constructors=4 if equality else 3,
        variable_payload_bits=payload_bits, opcode_bits=opcode_bits,
        framing_bits=len(bits) - payload_bits - opcode_bits, total_bits=len(bits))
    if include_encoding: out |= {'rpn': tokens, 'binary_frame': bits}
    return out


def report() -> dict:
    abstract = templates()
    concrete = templates(Mem(0, 1))
    rows = {}
    for name, template in abstract.items():
        actual = concrete[name]
        compact = alpha_reuse(normalize(actual))
        rows[name] = {
            'template_raw_negation_basis': metrics(template),
            'template_dn_normalized': metrics(normalize(template)),
            'template_source02_bottom_basis': metrics(bottom_basis(template)),
            'concrete_Mem_0_1_raw': encoding_metrics(actual),
            'concrete_Mem_0_1_dn_alpha_reused': encoding_metrics(compact,
                include_encoding=name in ('CG_oneway', 'PSC_subset_subset')),
        }
    totals = {name: {mode: sum(rows[a][mode]['nodes'] for a in axioms)
        for mode in ('template_raw_negation_basis', 'template_dn_normalized',
                     'template_source02_bottom_basis')} | {
        'concrete_separate_frames_dn_alpha_bits': sum(rows[a]['concrete_Mem_0_1_dn_alpha_reused']['total_bits'] for a in axioms),
        'axioms': axioms,
        } for name, axioms in THEORIES.items()}
    return {
        'scope': 'Executable formula generation and encoding only; not a proof checker, compiler, machine, state estimate, or minimality result.',
        'credits': 'Intake sources01--03; source02 raw bottom-basis reference; new subset-only research and one-way congruence comparison.',
        'template_basis': 'mem,eq,hole,not,imp,all; each hole occurrence counts one leaf; parameter closure absent for the parameter-free abstract matrix.',
        'normalization': 'Classical double-negation cancellation only; raw source02 reference performs no cancellation.',
        'congruence_equivalence': 'The symmetric conclusion implies one-way CG. Conversely D(x,y) is symmetric; instantiate universal one-way CG at (y,x) to obtain the reverse membership implication, then conjoin both directions. Finite tests are regressions, not the universal proof.',
        'concrete_matrix': ['mem', 0, 1],
        'concrete_warning': 'Mem(0,1) instantiates one matrix, not the infinite schema. No matrix holes are serialized. Parameter-bearing matrices are universally closed by the generators.',
        'binary_basis': 'NAND basis: mem,NAND,all (3), plus eq when needed (4); trees repeat subexpressions without DAG sharing.',
        'binary_format': 'Mode bit; Elias gamma(payload_bit_length+1); postfix tokens. Mode0 opcodes mem0,NAND10,all11; mode1 mem00,eq01,NAND10,all11. Each variable/binder label v uses gamma(v+1). Strict whole-frame decoding.',
        'exclusions': 'Formula encodings charge variable and binder payloads but exclude proof-engine/equality rules, schema recognizer, certificate grammar, search enumeration, targets, initialization, and TM backend. Separate axiom frames exclude a theory-list container.',
        'templates': rows, 'theories': totals,
    }


if __name__ == '__main__':
    result = report()
    output = Path(__file__).resolve().parent / 'results' / 'kernel_metrics.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['theories'], indent=2))
    print(f'Wrote {output}')
