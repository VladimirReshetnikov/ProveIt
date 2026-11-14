from pathlib import Path
import json, itertools, time
import router_fast as r
OUT = Path(__file__).resolve().parent
for source, scanner in [(r.P / 'grammar.json', False),
                        (OUT / 'pa195_scanner8/grammar.json', True)]:
    t = r.c.read_grammar(source)
    raw, ix, shape = r.c.build(t)
    if scanner:
        raw.update({(34, 0): (0, False, 1999),
                    (1999, 0): (0, False, 75), (1999, 1): (1, False, 2)})
    start = time.time()
    info = r.two_router_candidates(raw, shape)
    print('SCREEN', scanner, {k: val for k, val in info.items() if k != 'hits'},
          'hits', len(info['hits']), 'time', time.time() - start, flush=True)
    survivors, checks = [], 0
    for ga, gb, upper in info['hits']:
        for ha, hb in itertools.product(ga, gb):
            checks += 1
            found = r.exact_folds(raw, shape, [ha, hb], info['target_folds'])
            if found is None:
                continue
            folded, fs, cert, rr = found
            name = ('s8_' if scanner else '') + 'routers194_' + '_'.join(map(str, ha + hb))
            (OUT / (name + '.native.tm')).write_bytes(r.v.table_bytes(folded))
            (OUT / (name + '.folds.json')).write_text(json.dumps(fs, indent=2))
            (OUT / (name + '.certificate.json')).write_text(json.dumps(cert, indent=2))
            sites, cfg, contracts = r.c.source(t)
            runtime = r.c.validate(folded, contracts)
            item = {'name': name, 'helpers': [ha, hb], 'folds': len(fs), 'runtime': runtime}
            survivors.append(item)
            print('LOCAL_SURVIVOR', scanner, item, flush=True)
    info['hits'] = len(info['hits'])
    info['exact_checks'] = checks
    info['survivors'] = survivors
    info['seconds'] = time.time() - start
    (OUT / ('scanner8_two_routers.json' if scanner else 'two_routers.json')).write_text(
        json.dumps(info, indent=2))
    print('DONE', scanner, info, flush=True)
