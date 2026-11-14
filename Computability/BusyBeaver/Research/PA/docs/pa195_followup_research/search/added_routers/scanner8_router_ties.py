"""One/two added-router screens for scanner-eight cost60 grammar ties."""
from pathlib import Path
import itertools, json, time, sys
import router_fast as r
import optimize_grammar as o
OUT = Path(__file__).resolve().parent
files = [Path(x) for x in sys.argv[1:]] or [
    (Path(__file__).resolve().parent / 'scanner821101.ndjson'),
    OUT / 'scanner_cross21202.ndjson']
symbols = json.loads((Path(__file__).resolve().parent / 'symbols.json').read_text())
symbols = [tuple(x) if isinstance(x, list) else x for x in symbols]
seen, results, winners = set(), [], []
started = time.time()


def fully_check(t, raw, shape, routers, target, tag):
    found = r.exact_folds(raw, shape, routers, target)
    if found is None:
        return None
    folded, folds, cert, with_helpers = found
    print('LOCAL_SURVIVOR', tag, routers, 'states', len(folded) // 2, flush=True)
    sites, cfg, contracts = r.c.source(t)
    source, emitter = r.v.source_binding(t, sites, cfg), r.v.emitter(t)
    raw_runtime = r.c.validate(raw, contracts)
    runtime = r.c.validate(folded, contracts)
    if not (raw_runtime['ok'] and runtime['ok']):
        print('RUNTIME_FAIL', tag, raw_runtime, runtime, flush=True)
        return None
    old, _ = r.c.machine()
    r.v.need(all(folded[q, b] == old[q, b]
                 for q in r.c.BOXSTATES for b in (0, 1)), 'oracle row modified')
    q, head, ones = 74, 0, set()
    for _ in range(59164):
        w, d, q = folded[q, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
    startup = json.loads((OUT / 'pa195_scanner8/startup_certificate.json').read_text())
    r.v.need(q == 84 and head == -2 and sorted(ones) == startup['complete_one_positions'],
             'exact scanner8 startup')
    labels = [74] + sorted({q for q, b in folded} - {74}) + [254]
    rev = {q: i for i, q in enumerate(labels)}
    dense = {(rev[q], b): (w, d, rev[n]) for (q, b), (w, d, n) in folded.items()}
    name = f's8_router{len(folded)//2}_{tag}'
    o.writegrammar(t, OUT / (name + '.json'))
    (OUT / (name + '.native.tm')).write_bytes(r.v.table_bytes(folded))
    (OUT / (name + '.tm')).write_bytes(r.v.table_bytes(dense))
    (OUT / (name + '.raw.tm')).write_bytes(r.v.table_bytes(raw))
    (OUT / (name + '.helpers.tm')).write_bytes(r.v.table_bytes(with_helpers))
    (OUT / (name + '.folds.json')).write_text(json.dumps(folds, indent=2))
    (OUT / (name + '.certificate.json')).write_text(json.dumps(cert, indent=2))
    info = {'name': name, 'routers': routers, 'target_folds': target,
            'states': len(folded) // 2, 'source': source, 'emitter': emitter,
            'raw_runtime': raw_runtime, 'runtime': runtime, 'startup': startup,
            'labels': labels}
    (OUT / (name + '.validation.json')).write_text(json.dumps(info, indent=2))
    print('SUCCESS', name, flush=True)
    return info


for file in files:
    for line_no, line in enumerate(file.read_text().splitlines()):
        rec = json.loads(line)
        built = []
        def get(i):
            return symbols[-i - 1] if i < 0 else built[i]
        for a, b in rec['rules']:
            built.append((get(a), get(b)))
        t = built[rec['root']]
        if t in seen:
            continue
        seen.add(t)
        raw, ix, shape = r.c.build(t)
        raw.update({(34, 0): (0, False, 1999),
                    (1999, 0): (0, False, 75), (1999, 1): (1, False, 2)})
        tag = f'{file.stem}_{line_no}'
        item = {'input': str(file), 'line': line_no, 'raw_states': len(raw) // 2}
        for helpers, screen in [(1, r.one_router_candidates), (2, r.two_router_candidates)]:
            report = screen(raw, shape)
            item[str(helpers)] = {k: val for k, val in report.items() if k != 'hits'}
            item[str(helpers)]['optimistic_hits'] = len(report['hits'])
            for hit in report['hits']:
                candidates = [[hit[0]]] if helpers == 1 else itertools.product(hit[0], hit[1])
                for routers in candidates:
                    winner = fully_check(t, raw, shape, routers, report['target_folds'],
                                         tag + '_' + str(helpers))
                    if winner is not None:
                        winners.append(winner)
                        break
        results.append(item)
        if len(results) % 10 == 0:
            print('PROGRESS', len(results), 'time', time.time() - started,
                  'winners', len(winners), flush=True)
final = {'unique_grammars': len(results), 'input_files': list(map(str, files)),
         'results': results, 'winners': winners, 'seconds': time.time() - started}
(OUT / 'scanner8_router_ties_results.json').write_text(json.dumps(final, indent=2))
print('DONE', len(results), 'winners', len(winners), 'time', time.time() - started, flush=True)
