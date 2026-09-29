"""Native-base-three stream transport: six operations, or eight with a bound.

Power geometry and the synchronized finite-controller path are hypotheses.
No radix dilation, Boolean-word predicate or whole-certificate count is hidden.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp
import explore_delayed_blank_raw_queue as predecessor


def digits(value, length):
    return [(value // 3**j) % 3 for j in range(length)]


def value(word):
    return sum(digit * 3**j for j, digit in enumerate(word))


def scalar_run(initial, appended, m, t):
    word = digits(initial, m)
    removed = []
    for a in digits(appended, t):
        removed.append(word[0])
        word = word[1:] + [a]
    return value(removed), value(word)


def scalar_gate():
    counts = dict(arbitrary_stream_tuples=0, admitted=0, noncausal_rejected=0,
                  t_zero_tuples=0, short_history_tuples=0,
                  forward_runs=0, zero_final_runs=0, short_zero_final_runs=0)
    for m in range(1, 4):
        W = 3**m
        for t in range(4):
            q = 3**t
            for initial in range(W):
                for appended in range(q):
                    actual_removed, final = scalar_run(initial, appended, m, t)
                    for removed in range(q):
                        arithmetic = removed == initial + W*appended
                        semantic = removed == actual_removed and final == 0
                        assert arithmetic == semantic
                        counts['arbitrary_stream_tuples'] += 1
                        counts['admitted'] += arithmetic
                        counts['noncausal_rejected'] += removed != actual_removed
                        counts['t_zero_tuples'] += t == 0
                        counts['short_history_tuples'] += t < m
    for m in range(1, 5):
        W = 3**m
        for t in range(7):
            q = 3**t
            for initial in range(W):
                for appended in range(q):
                    removed, final = scalar_run(initial, appended, m, t)
                    assert removed + q*final == initial + W*appended
                    assert (final == 0) == (initial + W*appended < q)
                    if final == 0:
                        assert removed == initial + W*appended
                        counts['zero_final_runs'] += 1
                        counts['short_zero_final_runs'] += t < m
                    counts['forward_runs'] += 1
    # A genuinely short zero-reaching run is valid in the general lemma.
    assert scalar_run(1, 0, 3, 1) == (1, 0)
    # Without the removed-word bound, a displayed identity can hide high digits.
    m, t, initial, appended = 2, 1, 3, 1
    W, q = 3**m, 3**t
    removed = initial + W*appended
    actual_removed, final = scalar_run(initial, appended, m, t)
    assert removed == 12 and removed >= q and actual_removed == 0 and final == 4
    counts['omitted_bound_counterexamples'] = 1
    return counts


def source_check(joint_bound=False):
    names = 'x L W alpha D0 D1 A0 A1 q beta'.split()
    symbols = dict(zip(names, sp.symbols(' '.join(names))))
    env = dict(symbols)
    dag = [('Wcalc', '*', 3, 'L'), ('input_bound', '+', 'x', 'alpha'),
           ('shiftA0', '*', 'W', 'A0'), ('read0', '+', 'x', 'shiftA0'),
           ('shiftA1', '*', 'W', 'A1'), ('read1', '+', 'L', 'shiftA1')]
    comparisons = [('W', 'Wcalc'), ('input_bound', 'L'), ('D0', 'read0'), ('D1', 'read1')]
    x, L, W, alpha, D0, D1, A0, A1, q, beta = [symbols[a] for a in names]
    sources = [W-3*L, x+alpha-L, D0-x-W*A0, D1-L-W*A1]
    if joint_bound:
        dag += [('read_sum', '+', 'D0', 'D1'), ('bound', '+', 'read_sum', 'beta')]
        comparisons.append(('bound', 'q'))
        sources.append(D0+D1+beta-q)
    for name, op, a, b in dag:
        a, b = env[a] if isinstance(a, str) else a, env[b] if isinstance(b, str) else b
        env[name] = a*b if op == '*' else a+b
    assert all(sp.expand(env[a]-env[b]-source) == 0
               for (a, b), source in zip(comparisons, sources))
    return dict(operations=len(dag), multiplications=sum(row[1] == '*' for row in dag),
                additions=sum(row[1] == '+' for row in dag), instructions=dag,
                comparisons=comparisons, sources=[sp.sstr(s) for s in sources],
                word_bound='paid D0+D1+beta=q with beta>0' if joint_bound else 'external 0<=D0,D1<q',
                unpaid_hypotheses=['L=3^ell', 'q=3^t', 'one common t-step finite-controller path on the four native streams'])


def native_history_gate():
    base = predecessor.old
    original_wrap, original_pack = predecessor.wrap, predecessor.pack_and_check
    context = {}
    counts = dict(histories=0, queue_steps=0, controller_replays=0,
                  scalar_replays=0, positive_stream_tuples=0,
                  zero_extensions=0, joint_bounds_already_strict=0,
                  final_delimiter_bounds=0,
                  native_wide_differences=0, max_native_exponent=0)

    def tracked_wrap(machine):
        wrapped = original_wrap(machine)
        context['machine'] = wrapped
        return wrapped

    def native_pack(rows, R, W, x, L):
        wide_power = original_pack(rows, R, W, x, L)
        t = len(rows)
        q = 3**t
        ell, power = 0, 1
        while power < L:
            ell, power = ell+1, power*3
        assert power == L and W == 3*L and x < L
        m = ell+1
        D = [sum(removed[i]*3**j for j, (_, removed, _) in enumerate(rows)) for i in range(2)]
        A = [sum(appended[i]*3**j for j, (_, _, appended) in enumerate(rows)) for i in range(2)]
        assert all(0 < v < q for v in D+A)
        assert D[0] == x+W*A[0] and D[1] == L+W*A[1]
        assert q > L and t >= m
        assert rows[-1][1] == base.DELIM and rows[-1][2] == base.PLAIN[0]
        assert D[0]+D[1] <= q-2
        counts['final_delimiter_bounds'] += 1
        counts['positive_stream_tuples'] += 1
        # Decode from the four native integers, not from the stored row heads.
        machine = context['machine']
        state, table, _ = machine.compile()
        word = tuple(base.PLAIN[x//3**j % 3] for j in range(ell))+(base.DELIM,)
        for j in range(t):
            removed = tuple(D[i]//3**j % 3 for i in range(2))
            appended = tuple(A[i]//3**j % 3 for i in range(2))
            assert removed == word[0]
            nxt, emitted, event = table[state, removed]
            assert emitted == appended
            state, word = nxt, word[1:]+(appended,)
            assert len(word) == m
            assert all(a == base.PLAIN[0] for a in word) == (state.kind == 'accept')
        assert state.kind == 'accept' and all(a == base.PLAIN[0] for a in word)
        counts['controller_replays'] += 1
        for i, initial in enumerate((x, L)):
            assert scalar_run(initial, A[i], m, t) == (D[i], 0)
            counts['scalar_replays'] += 1
        # One genuine accepted zero-loop supplies the paid joint-bound variant.
        nxt, emitted, event = table[state, base.PLAIN[0]]
        assert nxt == state and emitted == base.PLAIN[0]
        assert D[0]+D[1] < 3*q and 3*q-D[0]-D[1] > 0
        assert value(digits(D[0], t)+[0]) == D[0]
        assert value(digits(A[0], t)+[0]) == A[0]
        counts['joint_bounds_already_strict'] += D[0]+D[1] < q
        counts['zero_extensions'] += 1
        wideD0 = sum(removed[0]*R**j for j, (_, removed, _) in enumerate(rows))
        counts['native_wide_differences'] += D[0] != wideD0
        counts['histories'] += 1
        counts['queue_steps'] += t
        counts['max_native_exponent'] = max(counts['max_native_exponent'], t)
        return wide_power

    # Temporary in-process test hooks collect genuine predecessor runs and
    # retain every predecessor arithmetic check; no dependency file is edited.
    predecessor.wrap, predecessor.pack_and_check = tracked_wrap, native_pack
    try:
        loader = predecessor.exhaustive_loader()
        runs = predecessor.runs()
    finally:
        predecessor.wrap, predecessor.pack_and_check = original_wrap, original_pack
    assert counts['histories'] == loader['positive_transports']+runs['positive_transports'] == 463
    assert counts['controller_replays'] == counts['zero_extensions'] == counts['histories']
    return dict(native_checks=counts, inherited_loader_counts=loader, inherited_run_counts=runs)


def dependency_hashes():
    root = Path(__file__).resolve().parents[1]
    paths = ('1980/EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md',
             'verification/explore_delayed_blank_raw_queue.py',
             'verification/explore_delayed_blank_raw_queue.json')
    return {relative: hashlib.sha256((root/relative).read_bytes().replace(b'\r\n', b'\n')).hexdigest()
            for relative in paths}


def verify():
    return dict(status='PASS_NATIVE_STREAM_RAW_QUEUE_COMPONENT',
                six_operation_source=source_check(), eight_operation_source=source_check(True),
                scalar_queue_lemma=scalar_gate(), native_machine_runs=native_history_gate(),
                dependency_canonical_lf_sha256=dependency_hashes(),
                proof='../1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md',
                scope='Exact causal native-base-three queue streams with conditional6-operation and explicitly bounded8-operation interfaces. Finite-controller arithmetic, power geometry and radix dilation are not compiled; no complete universal operation bound is asserted.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(path.read_text(encoding='utf-8')) == json.loads(json.dumps(result))
    print(result['status'], result['six_operation_source']['operations'], result['eight_operation_source']['operations'])
    print(result['scalar_queue_lemma'])
    print(result['native_machine_runs']['native_checks'])
