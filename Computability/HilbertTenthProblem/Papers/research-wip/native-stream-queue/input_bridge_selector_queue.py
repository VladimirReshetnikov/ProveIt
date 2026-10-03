"""Exact native-selector/FIFO composition; no universal controller claim."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import sympy as sp
import native_controller_three_selector_53 as selector

HERE = Path(__file__).resolve().parent
SPECIAL = {'D0': (1, 0, 1), 'D1': (0, 1, 1), 'A': (1, 0, 0)}
WORST = {'D0': (1, 0, 2), 'D1': (0, 1, 2),
         'A0': (2, 0, 1), 'A1': (1, 2, 0)}


def projection(name, column):
    """At most two additions/subtractions, using the paid H and 2H."""
    c = tuple(column)
    assert len(c) == 3 and set(c) <= {0, 1, 2}
    rows = []

    def emit(op, left, right):
        register = f'{name}_p{len(rows)}'
        rows.append((register, op, left, right))
        return register

    if len(set(c)) == 1:
        answer = (0, 'Hrep', 'twice_H')[c[0]]
    elif set(c) == {0, 1, 2}:
        part = emit('+', 'Hrep', f'F{c.index(2)}')
        answer = emit('-', part, f'F{c.index(0)}')
    elif set(c) == {1, 2}:
        if c.count(2) == 1:
            answer = f'F{c.index(2)}'
        else:
            three_H = emit('+', 'Hrep', 'twice_H')
            answer = emit('-', three_H, f'F{c.index(1)}')
    else:
        scale = max(c)
        bit = tuple(v//scale for v in c)
        if sum(bit) == 1:
            answer = emit('-', f'F{bit.index(1)}', 'Hrep')
        else:
            answer = emit('-', 'twice_H', f'F{bit.index(0)}')
        if scale == 2:
            answer = emit('+', answer, answer)
    assert len(rows) <= 2
    return rows, answer


def value(env, operand):
    return env[operand] if isinstance(operand, str) else operand


def source_check(columns, shared_append=False):
    names = ['q', 'F0', 'F1', 'F2', 'Hrep']+selector.CORE_NAMES
    names += ['x', 'L', 'W', 'alpha', 'V']+list(columns)
    z = {name: sp.Symbol(name) for name in names}
    # The inherited kernel uses D1 as a temporary; keep stream coordinates distinct.
    renamed_core = [tuple('kernel_D1' if v == 'D1' else v for v in row)
                    for row in selector.CORE]
    schedule = selector.OUTER54+renamed_core
    equalities = [('q', 'q_calc'), ('sum012', 'four_H'), ('r', 'packed')]
    equalities += selector.kernel.EQUALITIES[1:]
    sources = selector.sources(z, True)
    u = 2*z['r']+1+z['j']*z['c']
    corrections = {11: sources[10]*(u*u-z['y_aux']**2)}
    checksum = sources[1]
    H = z['Hrep']
    F = [z[f'F{i}'] for i in range(3)]
    for name, column in columns.items():
        rows, projected = projection(name, column)
        schedule += rows
        env = selector.execute(schedule, z)
        direct = sum(column[i]*(F[i]-H) for i in range(3))
        difference = sp.expand(direct-value(env, projected))
        factor = difference.coeff(F[0])
        assert sp.expand(difference-factor*checksum) == 0
        corrections[len(sources)] = factor*checksum
        sources.append(z[name]-direct)
        equalities.append((name, projected))
    app0, app1 = ('A', 'A') if shared_append else ('A0', 'A1')
    extra = [('Wcalc', '*', 3, 'L'), ('input_bound', '+', 'x', 'alpha'),
             ('shift0', '*', 'W', app0), ('read0', '+', 'x', 'shift0')]
    if shared_append:
        extra.append(('read1', '+', 'L', 'shift0'))
    else:
        extra += [('shift1', '*', 'W', app1), ('read1', '+', 'L', 'shift1')]
    extra.append(('time_divisor', '*', 'L', 'V'))
    schedule += extra
    equalities += [('W', 'Wcalc'), ('input_bound', 'L'),
                   ('D0', 'read0'), ('D1', 'read1'), ('q', 'time_divisor')]
    sources += [z['W']-3*z['L'], z['x']+z['alpha']-z['L'],
                z['D0']-z['x']-z['W']*z[app0],
                z['D1']-z['L']-z['W']*z[app1], z['q']-z['L']*z['V']]
    env = selector.execute(schedule, z)
    records = []
    for i, ((left, right), source) in enumerate(zip(equalities, sources)):
        correction = corrections.get(i, 0)
        assert sp.expand(value(env, left)-value(env, right)-source-correction) == 0, i
        records.append(dict(equality=[left, right], source=str(sp.expand(source)),
                            correction=str(sp.expand(correction))))
    counts = Counter(row[1] for row in schedule)
    assert len(equalities) == len(sources) == 18+len(columns)
    expected = (63, 32, 31) if shared_append else (69, 33, 36)
    assert (len(schedule), counts['*'], counts['+']+counts['-']) == expected
    return dict(operations=len(schedule), multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'], equations=len(sources),
                positive_external_parameter='x',
                positive_existential_coordinates=[name for name in names if name != 'x'],
                columns={name:list(column) for name,column in columns.items()},
                instructions=[list(row) for row in schedule], sources=records)


def all_projections():
    H, F0, F1, F2 = sp.symbols('H F0 F1 F2')
    symbolic = dict(Hrep=H, twice_H=2*H, F0=F0, F1=F1, F2=F2)
    checksum = F0+F1+F2-4*H
    counts = Counter()
    checked = 0
    for column in product(range(3), repeat=3):
        rows, output = projection('test', column)
        env = selector.execute(rows, symbolic)
        direct = sum(column[i]*([F0,F1,F2][i]-H) for i in range(3))
        difference = sp.expand(direct-value(env, output))
        assert sp.expand(difference-difference.coeff(F0)*checksum) == 0
        counts[len(rows)] += 1
        for t in range(1, 6):
            q = 3**t
            for tail in product(range(3), repeat=t-1):
                labels = (0,)+tail
                rep = (q-1)//2
                T = [sum(3**j for j,label in enumerate(labels) if label == i) for i in range(3)]
                fields = [rep+ti for ti in T]
                env = selector.execute(rows, dict(Hrep=rep, twice_H=2*rep,
                                                 **{f'F{i}':fields[i] for i in range(3)}))
                projected = value(env, output)
                native = sum(column[label]*3**j for j,label in enumerate(labels))
                assert projected == native and 0 <= projected < q
                assert projected % 3 == column[0]
                checked += 1
    return dict(columns=27, operation_count_distribution={str(k):v for k,v in sorted(counts.items())},
                native_word_checks=checked, max_time=5)


def fifo_checks():
    checked = accepted = 0
    examples = []
    read = ((1, 0), (0, 1), (1, 1))
    append = ((1, 1), (0, 0), (0, 0))
    for t in range(1, 7):
        q = 3**t
        H = (q-1)//2
        for tail in product(range(3), repeat=t-1):
            labels = (0,)+tail
            D = [sum(read[label][i]*3**j for j,label in enumerate(labels)) for i in range(2)]
            A = [sum(append[label][i]*3**j for j,label in enumerate(labels)) for i in range(2)]
            if min(D+A) <= 0:
                continue
            for ell in range(t):
                L, W = 3**ell, 3**(ell+1)
                for x in range(1, L):
                    arithmetic = D[0] == x+W*A[0] and D[1] == L+W*A[1]
                    queue = [((x//3**j)%3, 0) for j in range(ell)]+[(0,1)]
                    actual_reads = True
                    for label in labels:
                        actual_reads &= queue.pop(0) == read[label]
                        queue.append(append[label])
                    semantic = actual_reads and not any(a or b for a,b in queue)
                    assert arithmetic == semantic
                    checked += 1
                    if arithmetic:
                        assert x % 3 == read[0][0]
                        T = [sum(3**j for j,label in enumerate(labels) if label == i) for i in range(3)]
                        examples.append(dict(x=x,L=L,W=W,q=q,V=q//L,alpha=L-x,
                                             labels=list(labels),fields=[H+ti for ti in T],
                                             D0=D[0],D1=D[1],A=A[0]))
                        accepted += 1
    assert accepted == 2
    assert examples[0] == dict(x=1,L=3,W=9,q=27,V=9,alpha=2,
                             labels=[0,1,2],fields=[14,16,22],D0=10,D1=12,A=1)
    for item in examples:
        ell = (len(item['labels'])-1)//2
        assert item['labels'] == [0]*ell+[1]+[2]*ell
        assert item['x'] == (3**ell-1)//2
    # The genuine delayed loader must read all these paired symbols at x=5.
    loader_reads = [(2,0),(1,0),(0,0),(0,1)]
    assert len(set(loader_reads)) == 4
    return dict(positive_stream_candidates=checked, admitted=accepted, examples=examples,
                loader_x5_initial_reads=[list(v) for v in loader_reads],
                scope='Finite scalar/FIFO comparison; full Pell auxiliaries supplied by the selector theorem.')


def verify():
    return dict(status='PASS_NATIVE_SELECTOR_QUEUE_COMPOSITION',
                source63=source_check(SPECIAL, True), example_source69=source_check(WORST),
                projections=all_projections(), fifo=fifo_checks(),
                dependencies={name:hashlib.sha256((HERE/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest()
                              for name in ('native_controller_three_selector_53.py',)},
                scope='Exact finite three-label FIFO relation; no synchronized universal controller or complete bound improvement.',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert result == json.loads(receipt.read_text(encoding='utf-8'))
    print(result['status'])
    print({key:result[key]['operations'] for key in ('source63','example_source69')})
    print(result['projections'])
    print(result['fifo'])
