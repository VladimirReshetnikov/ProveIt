# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Own bounded read-only tests of the emitted literal tables, not upstream code."""
from collections import Counter, deque
from pathlib import Path
import hashlib, json, random
ROOT = Path(__file__).resolve().parent

def run():
    raw = (ROOT / 'literal_tables.json').read_bytes()
    p = json.loads(raw)
    tag = p['tag']
    g = p['genera']
    states = p['refined_states']
    names = {r['id']: r['name'] for r in tag['alphabet']}
    ids = {v: k for k, v in names.items()}
    rules = {r['symbol']: tuple(r['output']) for r in tag['productions']}
    gn = {r['id']: r['name'] for r in g['alphabet']}
    gi = {v: k for k, v in gn.items()}
    gr = {r['id']: r for r in g['alphabet']}
    d = g['dummy_symbol']
    H = tag['accepting_symbol']
    GH = g['halt_symbol']

    def canonical(i, M, N, which=tag):
        v = which['canonical_symbols'][str(i)]
        return [v['A'], v['x']] + [v['a'], v['x']] * M + [v['B'], v['x']] + [v['b'], v['x']] * N

    def oracle(i, M, N):
        row = states[i]
        if row['accepting']:
            return None
        s = row['write']
        v = (M if row['direction'] == 'L' else N) % 2
        j = row['next_if_one' if v else 'next_if_zero']
        return (j, M // 2, 2 * N + s) if row['direction'] == 'L' else (j, 2 * M + s, N // 2)

    def macro(i, M, N):
        expected = oracle(i, M, N)
        target = canonical(*expected)
        q = deque(canonical(i, M, N))
        steps = 0
        minimum = len(q)
        while not (steps and names[q[0]].startswith('A:')):
            if not len(q) >= 2:
                raise RuntimeError('Invariant failed at original source line 27')
            a = q.popleft()
            q.popleft()
            if not not names[a].startswith('x:'):
                raise RuntimeError('Invariant failed at original source line 28')
            if not (a != H and (not a == ids['A:19'])):
                raise RuntimeError('Invariant failed at original source line 29')
            q.extend(rules[a])
            steps += 1
            minimum = min(minimum, len(q))
            if not steps < 1000000:
                raise RuntimeError('Invariant failed at original source line 30')
        if not list(q) == target:
            raise RuntimeError((i, M, N, expected, list(q), target))
        return (expected, steps, minimum)

    def ugeneration(word, phase):
        out = []
        for a in word:
            if phase == 0:
                out.extend(rules[a])
            phase ^= 1
        return (out, phase)

    def add(out, a, n=1):
        if not n:
            return
        if out and out[-1][0] == a:
            out[-1] = (a, out[-1][1] + n)
        else:
            out.append((a, n))

    def rle(word):
        out = []
        for a in word:
            add(out, a)
        return out

    def ngen(word, phase):
        out = []
        for a, n in word:
            row = gr[a]
            if not a != GH:
                raise RuntimeError('Invariant failed at original source line 51')
            if row['width'] == 0:
                b, c = row['productions'][phase]
                if b == c:
                    add(out, b, 2 * n)
                else:
                    if not n <= 100000:
                        raise RuntimeError('Invariant failed at original source line 56')
                    for _ in range(n):
                        add(out, b)
                        add(out, c)
            else:
                if not n <= 100000:
                    raise RuntimeError('Invariant failed at original source line 59')
                for _ in range(n):
                    for b in row['productions'][phase]:
                        add(out, b)
                    phase ^= 1
        return (out, phase)

    def erase(word):
        out = []
        for a, n in word:
            if a != d:
                if not gr[a]['kind'] in ('original', 'halt'):
                    raise RuntimeError('Invariant failed at original source line 68')
                out.extend([ids[gn[a]]] * n)
        return out
    checks = Counter()
    minimum = 10 ** 9
    total_steps = 0
    for row in states:
        i = row['id']
        if row['accepting']:
            continue
        for M in range(10):
            for N in range(10):
                _, steps, m = macro(i, M, N)
                checks['actual_row_macro_cases'] += 1
                total_steps += steps
                minimum = min(minimum, m)
    rng = random.Random(1013570)
    visits = set()
    max_integer = 0
    for row in states:
        if row['accepting']:
            continue
        for seed in range(12):
            cfg = (row['id'], rng.randrange(9), rng.randrange(9))
            checks['multistep_seed_cases'] += 1
            for step in range(8):
                i, M, N = cfg
                if i == 19:
                    q = canonical(i, M, N)
                    out, p1 = ugeneration(q, 0)
                    if not out.count(H) == 1:
                        raise RuntimeError('Invariant failed at original source line 89')
                    checks['multistep_accepting_endpoints'] += 1
                    break
                visits.add(i)
                max_integer = max(max_integer, M, N)
                cfg, t, m = macro(i, M, N)
                checks['multistep_transitions'] += 1
                total_steps += t
                minimum = min(minimum, m)
    originals = g['original_symbols']
    for case in range(400):
        phase = case % 2
        word = []
        plain = []
        for _ in range(1 + case % 9):
            add(word, d, rng.randrange(1, 33))
            a = rng.choice(originals)
            add(word, a)
            plain.append(ids[gn[a]])
        add(word, d, rng.randrange(1, 33))
        first, p1 = ngen(word, phase)
        second, p2 = ngen(first, p1)
        wanted, p3 = ugeneration(plain, phase)
        if not (erase(second) == wanted and p2 == p3):
            raise RuntimeError('Invariant failed at original source line 105')
        if not sum((n for _, n in second)) == 4 * sum((n for _, n in word)):
            raise RuntimeError('Invariant failed at original source line 106')
        checks['two_generation_projection_cases'] += 1
    traces = []
    for i in (17, 19):
        for M in range(8):
            if i == 17 and M % 2 == 0:
                continue
            for N in range(8):
                q = rle(canonical(i, M, N, g))
                base = canonical(i, M, N)
                phase = 0
                basephase = 0
                gen = 0
                maxruns = len(q)
                initial_length = sum((n for _, n in q))
                while not any((a == GH for a, _ in q)):
                    q, phase = ngen(q, phase)
                    gen += 1
                    maxruns = max(maxruns, len(q))
                    if not sum((n for _, n in q)) == initial_length * 2 ** gen:
                        raise RuntimeError('Invariant failed at original source line 119')
                    if gen % 2 == 0:
                        base, basephase = ugeneration(base, basephase)
                        if not (erase(q) == base and phase == basephase):
                            raise RuntimeError('Invariant failed at original source line 122')
                    if not gen <= 30:
                        raise RuntimeError('Invariant failed at original source line 123')
                if not (gen % 2 == 0 and sum((n for a, n in q if a == GH)) == 1):
                    raise RuntimeError('Invariant failed at original source line 124')
                hpos = 0
                for a, n in q:
                    if a == GH:
                        break
                    if not gr[a]['kind'] in ('original', 'dummy'):
                        raise RuntimeError('Invariant failed at original source line 128')
                    if not all((GH not in w for w in gr[a]['productions'])):
                        raise RuntimeError('Invariant failed at original source line 129')
                    hpos += n
                checks['normalized_unique_H_cases'] += 1
                traces.append(dict(refined_state=i, M=M, N=N, first_H_generation=gen, first_H_index=hpos, halt_generation_length=sum((n for _, n in q)), final_phase=phase, max_compressed_runs=maxruns))
    pairmap = {tuple(r['expands']): r['id'] for r in g['alphabet'] if r['kind'] == 'pair'}
    dd = pairmap[d, d]
    for a in originals:
        rawprod = [gi[names[x]] for x in rules[ids[gn[a]]]]
        w = rawprod + [d] * (4 - len(rawprod))
        if not gr[a]['width'] == 1:
            raise RuntimeError('Invariant failed at original source line 141')
        if not gr[a]['productions'] == [[pairmap[tuple(w[:2])], pairmap[tuple(w[2:])]], [dd, dd]]:
            raise RuntimeError('Invariant failed at original source line 142')
        checks['all_original_normalization_rows'] += 2
    for row in g['alphabet']:
        if not (len(row['productions']) == 2 and all((len(w) == 2 for w in row['productions']))):
            raise RuntimeError('Invariant failed at original source line 145')
        if row['kind'] == 'pair':
            if not (row['width'] == 0 and row['productions'] == [row['expands'], row['expands']]):
                raise RuntimeError('Invariant failed at original source line 147')
            checks['all_pair_expansion_rows'] += 2
    return dict(status='PASS_LITERAL_BOUNDED_CHECKS', checks=dict(checks), counts=p['counts'], all_nonhalt_states_visited=sorted(visits), total_literal_tag_steps=total_steps, minimum_preacceptance_word=minimum, maximum_counter_in_multistep_tests=max_integer, normalized_halting_traces=traces, literal_tables_sha256=hashlib.sha256(raw).hexdigest(), checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), exclusions=['No primary or upstream Python executed.', 'No arithmetic/history circuit emitted.', 'No finite tests are claimed to prove universality.', 'No Pell witnesses materialized.'])
if __name__ == '__main__':
    result = run()
    (ROOT / 'literal_checks.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('normalized_halting_traces', 'counts')}, sort_keys=True))
