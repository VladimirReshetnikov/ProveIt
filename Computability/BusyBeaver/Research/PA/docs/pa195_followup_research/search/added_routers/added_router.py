"""Add one preserved-bit R/R router, seek at least two extra compatible folds."""
from pathlib import Path
import collections, itertools, json, sys, time
P = (Path(__file__).resolve().parent / 'reference_pa195')
sys.path.insert(0, str(P))
import build_verify as v
c = v.c
OUT = Path(__file__).resolve().parent
is8 = '--scanner8' in sys.argv
ignore_new = '--ignore-new-incoming' in sys.argv
S = OUT / 'pa195_scanner8' if is8 else P
t = c.read_grammar(S / 'grammar.json')
raw, index, shape = c.build(t)
if is8:
    raw[34, 0] = (0, False, 1999)
    raw[1999, 0] = (0, False, 75)
    raw[1999, 1] = (1, False, 2)
states = {q for q, b in raw}
Q = 1998
v.need(Q not in states, 'new router label collision')
incoming = collections.defaultdict(set)
for (q, b), (w, d, n) in raw.items():
    incoming[n].add((w, d))
left = [q for q in shape if incoming[q] == {(0, True)}]
right = [q for q in shape if incoming[q] == {(1, True)}]
byact = [collections.defaultdict(list), collections.defaultdict(list)]
for q in states:
    for bit in (0, 1):
        byact[bit][raw[q, bit]].append(q)
candidates = set()
for a, b in itertools.product(left, right):
    for bit in (0, 1):
        if raw[a, bit] == raw[b, bit]:
            continue
        for u, w in itertools.product(byact[bit][raw[a, bit]], byact[bit][raw[b, bit]]):
            if not {a, b} & {u, w}:
                candidates.add((u, w))


def find_folds(rows, ops, target):
    # Exhaustively enumerate compatible disjoint edge sets at the required size;
    # a fixed maximum matching can miss a compatible alternative matching.
    used, fs = set(), []
    attempts = 0
    answer = None
    def search(i):
        nonlocal attempts, answer
        if len(fs) == target:
            attempts += 1
            try:
                folded, aliases = v.quotient(rows, fs)
                # In the broader mode the helper is absent from the simulated
                # raw machine. It is used only inside the explicitly checked
                # folded detours; its outgoing rows need no raw-entry premise.
                cert_rows = raw if ignore_new else rows
                cert = v.quotient_certificate(cert_rows, folded, fs, aliases)
                answer = (folded, [list(f) for f in fs], cert)
                return True
            except (ValueError, KeyError):
                return False
        if len(fs) + len(ops) - i < target:
            return False
        a, b, choices = ops[i]
        if a not in used and b not in used:
            used.update((a, b))
            for acts in itertools.product(*choices):
                fs.append((a, b, acts))
                if search(i + 1):
                    return True
                fs.pop()
            used.difference_update((a, b))
        return search(i + 1) if i + 1 < len(ops) else False
    if len(ops) >= target:
        search(0)
    return answer, attempts


target = len(raw) // 2 + 1 - 194
print('BEGIN', 'scanner8' if is8 else 'original', 'ignore_new', ignore_new,
      'routers', len(candidates),
      'target_folds', target, flush=True)
best = 1000
screened, exact_checks, local_survivors = 0, 0, []
started = time.time()
sites, cfg, contracts = c.source(t)
for u, w in sorted(candidates):
    rows = raw.copy()
    rows[Q, 0] = (0, True, u)
    rows[Q, 1] = (1, True, w)
    ops = c.opportunities_fast(rows, shape, ignore_incoming={Q} if ignore_new else frozenset())
    upper = len(c.max_matching(ops))
    optimistic_states = len(rows) // 2 - upper
    screened += 1
    if optimistic_states < best:
        best = optimistic_states
        print('BEST', best, 'router', u, w, 'ops', len(ops), 'folds', upper, flush=True)
    if upper < target:
        continue
    found, tries = find_folds(rows, ops, target)
    exact_checks += tries
    if found is None:
        continue
    folded, fs, cert = found
    print('LOCAL_SURVIVOR', u, w, len(fs), 'states', len(folded) // 2, flush=True)
    runtime = c.validate(folded, contracts)
    info = {'router': [Q, u, w], 'states': len(folded) // 2,
            'folds': fs, 'local_cases': cert['local_cases'], 'runtime': runtime}
    local_survivors.append(info)
    if not runtime['ok']:
        print('RUNTIME_FAIL', runtime, flush=True)
        continue
    q, head, ones = 74, 0, set()
    try:
        for _ in range(59164 if is8 else 58154):
            ww, dd, q = folded[q, int(head in ones)]
            (ones.add if ww else ones.discard)(head)
            head += 1 if dd else -1
    except KeyError:
        continue
    seed = json.loads((S / 'startup_certificate.json').read_text())
    if q != 84 or head != -2 or sorted(ones) != seed['complete_one_positions']:
        print('STARTUP_FAIL', u, w, flush=True)
        continue
    labels = [74] + sorted({q for q, b in folded} - {74}) + [254]
    rev = {q: i for i, q in enumerate(labels)}
    dense = {(rev[q], b): (ww, dd, rev[n]) for (q, b), (ww, dd, n) in folded.items()}
    name = ('s8_' if is8 else '') + ('broader_' if ignore_new else '') + f'router194_{u}_{w}'
    (OUT / (name + '.native.tm')).write_bytes(v.table_bytes(folded))
    (OUT / (name + '.tm')).write_bytes(v.table_bytes(dense))
    (OUT / (name + '.folds.json')).write_text(json.dumps(fs, indent=2))
    (OUT / (name + '.certificate.json')).write_text(json.dumps(cert, indent=2))
    info.update({'startup': seed, 'labels': labels})
    (OUT / (name + '.validation.json')).write_text(json.dumps(info, indent=2))
    print('SUCCESS', name, flush=True)
result = {'router_candidates': len(candidates), 'screened': screened,
          'ignore_unreachable_helper_incoming': ignore_new,
          'optimistic_best': best, 'target_folds': target,
          'exact_compatible_cases_checked': exact_checks,
          'local_survivors': local_survivors, 'seconds': time.time() - started}
(OUT / (('scanner8_' if is8 else '') + ('broader_' if ignore_new else '') + 'router_results.json')).write_text(
    json.dumps(result, indent=2))
print('DONE', json.dumps(result), flush=True)
