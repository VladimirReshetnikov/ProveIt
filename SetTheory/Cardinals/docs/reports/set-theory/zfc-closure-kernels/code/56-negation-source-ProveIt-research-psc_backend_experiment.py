"""Compile the PSC template on scratch, with an explicitly incomplete calculus.

The pinned Wade backend is copied unchanged to scratch. This experiment never
edits the frozen252 candidate, core generator, imports, or Lean files. Its
primitive-Bottom252 output has a dead-quantifier algebraic model; it is NOT a
calibrated ZFC-consistency machine. Exact macro-word sharing is checked.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import random
import sys
from functools import cache

from recover_wade_dag import ROOT, COMMIT, REGISTERS, builder_from_dag, git_bytes, parse_dag
from pairing_backend_experiment import execute_helper
from theory_backend_experiment import (Imp, Rel, All, Not, And, Ex, Or, TAIL,
    MACROS, emit as old_emit, lower_program, old_contract, published_spec)
import psc_adapter_checks

INC = '3.topwff.inc'


def closed_macro_checks(nodes):
    @cache
    def bounds(edge):
        kind, *payload = edge.split()
        n = int(payload[0]) if payload else 0
        if kind == 'ENode':
            left, right = map(bounds, nodes[n])
            return max(left[0]-1, right[0], 0), max(left[1], right[1]-1, 0)
        if kind == 'EDecnz': return 1, 0
        if kind == 'EBreak': return n, 0
        if kind == 'EContinue': return 0, n
        return 0, 0
    for q in MACROS:
        if bounds(f'ENode {q}') != (0,0):
            raise ValueError(f'macro {q} can escape reassociated sequence control')
    return len(MACROS)


def emit(p):
    if p == 'k':
        return [168, INC, INC]  # push c, then add2: binder k=c+2.
    if not isinstance(p, tuple):
        return old_emit(p)
    if p[0] == 'imp' and p[2] == 1:
        inner = p[1]
        if (isinstance(inner, tuple) and inner[0] in ('imp', 'all')
                and isinstance(inner[2], tuple) and inner[2][0] == 'imp'
                and inner[2][2] == 1):
            return emit(inner[1]) + emit(inner[2][1]) + [178 if inner[0] == 'imp' else 183]
        return emit(inner) + [218]
    return emit(p[1]) + emit(p[2]) + [{'imp': 119, 'rel': 181, 'all': 180}[p[0]]]


def psc_template(binder='k'):
    sub = lambda x, y, z: All(z, Imp(Rel(z, x), Rel(z, y)))
    sb = All(0, Ex(binder, All(1, Imp('c', sub(1, binder, 0)))))
    guard = Or(sub(0, 1, binder), Rel(0, binder))
    closed = All(0, Imp(guard, All(1, Imp('c', Rel(1, binder)))))
    support = All(1, Imp(Rel(1, binder), Ex(0, 'c')))
    return Imp(sb, All(1, Ex(binder, And(closed, support))))


def repair(word, seed):
    """Weighted exact-word Re-Pair, following delivered source08's idea."""
    rng, seq, grammar = random.Random(seed), list(word), []
    while True:
        counts = Counter(zip(seq, seq[1:]))
        choices = [(pair, f) for pair, f in counts.items() if f >= 2]
        if not choices:
            return seq, grammar
        pair = rng.choices([p for p, _ in choices], [f**4 for _, f in choices])[0]
        new, i = [], 0
        while i < len(seq):
            if i+1 < len(seq) and tuple(seq[i:i+2]) == pair:
                new.append(('g', len(grammar)))
                i += 2
            else:
                new.append(seq[i])
                i += 1
        if len(seq)-len(new) < 2:
            return seq, grammar
        grammar.append(pair)
        seq = new


def macro_expansion(builder, q):
    if not isinstance(q, int) or q in MACROS:
        return [q]
    return [v for child in builder.sequences[q].seq for v in macro_expansion(builder, child)]


def retag_bottom4(builder):
    # Historical wal(+2) now implements Rel; weq(+3) now implements All.
    # Their old names do not denote an equality operation in this experiment.
    for i, sequence in enumerate(builder.sequences):
        if i not in (180, 181, 182):
            sequence.seq = tuple({181: 180, 180: 182}.get(v, v)
                if isinstance(v, int) else v for v in sequence.seq)
    builder.reduce_to_cons()
    builder.name_sequences()


def build(backend, nodes, names, codec, order=(3, 1, 7, 5), seed=None,
          ir=False, gated=False, grouping='separate'):
    spec, _ = published_spec()
    rows = spec['ax_rows']('a', 'h', 'b', 'c', 'u')
    builder = builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    vr = Imp(Rel('a', 'b'), All('c', Rel('a', 'b')))
    psc = psc_template('c' if gated else 'k')
    program = [166, 121, 180, 176] + [m for i in order for m in emit(rows[i])]
    if grouping == 'separate':
        program += emit(psc)
        if gated:
            r = [builder.reg(n) for n in REGISTERS]
            clear = builder.while_decnz(r[1], ())
            program += [192, builder.while_decnz(r[7], r[3].inc),
                builder.if_not_decnz(r[6], clear), builder.if_not_decnz(r[6], clear),
                builder.while_decnz(r[6], ())]
        if ir:
            program += emit(All(1, Not(Rel(1, 1))))
        program += emit(vr)
    else:
        if gated or ir:
            raise ValueError('grouping control uses ungated PSC without IR')
        program += emit(And(psc, vr) if grouping == 'PSC_V' else And(vr, psc))
    program += TAIL
    if seed is None:
        lower_program(builder, nodes, program, f'PSC_{codec}', shared=True, base3=codec == 'base3')
    else:
        residual, grammar = repair(program, seed)
        refs = {}
        resolve = lambda x: refs[x] if isinstance(x, tuple) else x
        for i, pair in enumerate(grammar):
            refs['g', i] = builder.add_sequence([resolve(x) for x in pair])
        root = builder.add_sequence([resolve(x) for x in residual])
        builder.sequences[root].name = f'PSC_repair_{seed}().0'
        if macro_expansion(builder, root) != program:
            raise ValueError('Re-Pair changed expanded macro word')
        for i, sequence in enumerate(builder.sequences):
            if i != 1:
                sequence.seq = tuple(root if x == 1 else x for x in sequence.seq)
        builder.breakout_common_subsequences()
        builder.reduce_to_cons()
        builder.name_sequences()
        if macro_expansion(builder, root) != program:
            raise ValueError('backend sharing changed expanded macro word')
        if codec == 'base3':
            builder.sequences[118].seq = (157, builder.sequences[118].seq[1])
    if codec == 'bottom4':
        retag_bottom4(builder)
    return builder


def constructor_checks(builder):
    pair = lambda a, b: (a+b)*(a+b+1)//2+b
    count = 0
    for a, b, rest in itertools.product(range(5), range(5), (0, 1, 5)):
        for root, tag in ((119, 0), (180, 2), (182, 3)):
            values = [7, b, pair(a, rest), 0, 11, 13, 0, 0, 19]
            expected = [7, 4*pair(a, b)+tag, rest, 0, 11, 13, 0, 0, 19]
            if execute_helper(builder, root, values) != ('normal',) or values != expected:
                raise ValueError('primitive-Bottom constructor contract failed')
            count += 1
    return count


def record(builder, output):
    builder.generate()
    builder.tm.gc()
    states = {q for q, _ in builder.tm.states}
    builder.tm.save(str(output))
    return dict(working_states=len(states), decision_states=sum(not q[0].isdigit() for q in states),
        framework_states=sum(q[0].isdigit() for q in states), transition_rows=len(builder.tm.states),
        missing_rows=[[q, b] for q in sorted(states) for b in ('0', '1')
                      if (q, b) not in builder.tm.states], named_table_sha256=hashlib.sha256(output.read_bytes()).hexdigest())


def main():
    if not __debug__:
        raise RuntimeError('run without -O: adapter audits require assertions')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--scratch', type=Path, required=True)
    p.add_argument('--output-evidence', type=Path)
    p.add_argument('--search', action='store_true', help='repeat24-row/grouping and200-seed families')
    args = p.parse_args()
    scratch = args.scratch.resolve()
    if scratch == Path('/') or scratch == ROOT or ROOT in scratch.parents:
        p.error('scratch must be outside the repository')
    scratch.mkdir(parents=True, exist_ok=True)
    for name in ('TMBuilder.py', 'tm.py', 'tmdb.py', 'LICENSE.wade'):
        (scratch/name).write_bytes(git_bytes(None, 'ZF/generator/'+name))
    sys.path.insert(0, str(scratch))
    backend = importlib.import_module('TMBuilder')
    nodes, names = parse_dag(git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    old_contract(nodes)
    results = {}
    recipes = [('gated_base3', dict(codec='base3', gated=True, order=(1,7,5,3))),
        ('offset_base3', dict(codec='base3', order=(1,7,5,3))),
        ('offset_bottom4', dict(codec='bottom4', order=(1,7,5,3))),
        ('offset_base3_best_order', dict(codec='base3')),
        ('offset_bottom4_best_order', dict(codec='bottom4')),
        ('offset_bottom4_with_IR', dict(codec='bottom4', ir=True, order=(1,7,5,3))),
        ('offset_bottom4_repair93', dict(codec='bottom4', seed=93))]
    for name, kwargs in recipes:
        builder = build(backend, nodes, names, **kwargs)
        if name == 'offset_bottom4_repair93':
            helper_cases = constructor_checks(builder)
        results[name] = record(builder, scratch/(name+'.tm'))
    evidence = dict(upstream_commit=COMMIT, generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        adapter_sha256=hashlib.sha256(Path(psc_adapter_checks.__file__).read_bytes()).hexdigest(),
        adapter_checks=psc_adapter_checks.check(), primitive_bottom_codec=psc_adapter_checks.codec_checks(),
        control_closed_macro_roots=closed_macro_checks(nodes),
        primitive_bottom_constructor_cases=helper_cases,
        variants=results, old_rho6_retained=True, complete_FOL_calculus=False,
        new_ZFC_machine_or_state_bound_claimed=False)
    if args.search:
        searches = {}
        for codec, grouping in itertools.product(('base3','bottom4'), ('separate','PSC_V','V_PSC')):
            costs = Counter()
            for order in itertools.permutations((1,3,5,7)):
                b = build(backend,nodes,names,codec,order=order,grouping=grouping)
                b.generate(); b.tm.gc(); costs[len({q for q,_ in b.tm.states})] += 1
            searches[codec+'_'+grouping] = dict(sorted(costs.items()))
        costs = Counter()
        for seed in range(200):
            b=build(backend,nodes,names,'bottom4',seed=seed)
            b.generate();b.tm.gc();costs[len({q for q,_ in b.tm.states})] += 1
        searches['bottom4_raw_word_200_seeds']=dict(sorted(costs.items()))
        evidence['searches']=searches
    text=json.dumps(evidence,indent=2,sort_keys=True)+'\n'
    if args.output_evidence: args.output_evidence.write_text(text)
    print(text,end='')


if __name__ == '__main__':
    main()
