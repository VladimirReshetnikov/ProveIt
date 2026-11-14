"""Try h/u state merges with one transition row borrowed from each parent.

Unlike pure h->u aliases, these can change a surviving row. An unchanged
original trace avoids the modified states, so only affected contracts need
screening; every survivor must then replay all contracts and exact startup.
"""
import sys, json, time, collections, itertools
from pathlib import Path

P = (Path(__file__).resolve().parent / 'reference_pa195')
sys.path.insert(0, str(P))
import build_verify as v
c = v.c
OUT = Path(__file__).resolve().parent
scanner8 = '--scanner8' in sys.argv
S = OUT / 'pa195_scanner8' if scanner8 else P
rows = v.table(S / ('pa195_scanner8.native.tm' if scanner8 else 'pa195.native.tm'))
t = c.read_grammar(S / 'grammar.json')
sites, cfg, cs = c.source(t)
byh = collections.defaultdict(set)
for ci, cc in enumerate(cs):
    seen = set()
    v.need(c.run(rows, cc, observe=lambda s: seen.add(s[0])) is not None,
           'starting machine fails contract')
    for h in seen:
        byh[h].add(ci)
protected = c.BOXSTATES | {74} | {n for (q, b), (w, d, n) in rows.items()
                                    if q in c.BOXSTATES}
states = sorted({q for q, b in rows} - protected)
count, successes = 0, []
started = time.time()
for h, u in itertools.combinations(states, 2):
    checks = sorted(byh[h] | byh[u])
    for bit in (0, 1):
        # Alias h to u; use h's selected branch and u's other branch.
        if rows[h, bit] == rows[u, bit]:
            continue
        rr = {(q, b): (w, d, u if n == h else n)
              for (q, b), (w, d, n) in rows.items() if q != h}
        w, d, n = rows[h, bit]
        rr[u, bit] = w, d, u if n == h else n
        count += 1
        if any(c.run(rr, cs[ci]) is None for ci in checks):
            continue
        runtime = c.validate(rr, cs)
        v.need(runtime['ok'], 'affected contract filter unsound')
        print('SURVIVOR', h, u, bit, runtime, flush=True)
        q, head, ones = 74, 0, set()
        try:
            for _ in range(59164 if scanner8 else 58154):
                w, d, q = rr[q, int(head in ones)]
                (ones.add if w else ones.discard)(head)
                head += 1 if d else -1
        except KeyError:
            continue
        seed = json.loads((S / 'startup_certificate.json').read_text())
        if q != 84 or head != -2 or sorted(ones) != seed['complete_one_positions']:
            print('BAD_STARTUP', h, u, bit, flush=True)
            continue
        stem = ('s8_' if scanner8 else '') + f'mixed194_{h}_{u}_{bit}'
        labels = [74] + sorted({q for q, b in rr} - {74}) + [254]
        rev = {q: i for i, q in enumerate(labels)}
        dense = {(rev[q], b): (w, d, rev[n]) for (q, b), (w, d, n) in rr.items()}
        (OUT / (stem + '.native.tm')).write_bytes(v.table_bytes(rr))
        (OUT / (stem + '.tm')).write_bytes(v.table_bytes(dense))
        info = {'delete': h, 'keep': u, 'borrowed_bit': bit,
                'runtime': runtime, 'startup': seed, 'labels': labels}
        (OUT / (stem + '.validation.json')).write_text(json.dumps(info, indent=2))
        successes.append(info)
        print('SUCCESS', stem, flush=True)
    if count % 1000 in (0, 1):
        print('PROGRESS', count, 'time', time.time() - started, flush=True)
result = {'cases': count, 'eligible_states': states, 'successes': successes,
          'elapsed_seconds': time.time() - started}
name = 'scanner8_mixed_results.json' if scanner8 else 'mixed_results.json'
(OUT / name).write_text(json.dumps(result, indent=2))
print('DONE', json.dumps(result), flush=True)
