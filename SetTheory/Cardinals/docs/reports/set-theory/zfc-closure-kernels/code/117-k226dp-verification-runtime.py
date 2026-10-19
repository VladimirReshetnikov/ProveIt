#!/usr/bin/env python3
"""Re-prove every instruction case with the pinned generic symbolic engine.

The engine is retained byte for byte. Its historical CLI pins a different
source program; this adapter supplies the K-specific, independently audited
input validation and calls only its generic prove_blocks and case functions.
All naturals and all finite spare tails are quantified by induction, not sampled.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import build
sys.path.insert(0, str(ROOT/'vendor/proveit'))
import symbolic_runtime as engine

ENGINE = 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER = '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prove(table_path, sites_path, output):
    build.require(__debug__ and not sys.flags.optimize, 'Assertions must be enabled')
    build.require(digest(ROOT/'vendor/proveit/symbolic_runtime.py') == ENGINE, 'Changed proof engine')
    build.require(digest(ROOT/'vendor/proveit/independent_runtime.py') == HELPER, 'Changed engine helper')
    table = build.parse(table_path.read_bytes(), 95, 254)
    sites = json.loads(sites_path.read_text())
    root = build.source.tree(sites)
    build.require(sites == [list(x) for x in build.source.sites(root)], 'Source must be in tree order')
    metrics = build.source.metrics(root)
    build.require(metrics['maximum_depth'] <= 64, 'Program exceeds the frame width')
    build.require(all(op not in ('CB','CC') or arg >= 1 for pc,op,arg in sites), 'Zero control argument')
    # This independently enumerates all successors and rejects any nonzero
    # unread suffix. It is the no-stray-bit lemma used between two case proofs.
    ordered, graph, entry = build.source.graph(sites)
    build.require(entry == 0 and set(ordered[0][0]) == {'0'}, 'Unexpected initial leaf')
    expected = sum(2 if op == 'CD' else 1 for pc,op,arg in sites)
    output.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic(); cases = []; used = set()
    result = {
        'status':'IN_PROGRESS', 'table_sha256':digest(table_path), 'source_sha256':digest(sites_path),
        'engine_sha256':ENGINE, 'helper_sha256':HELPER, 'adapter_sha256':digest(Path(__file__)),
        'states':len(table)//2, 'rows':len(table), 'metrics':metrics, 'expected_cases':expected,
        'source_successor_no_stray_check':True, 'initial_leaf':ordered[entry][0],
        'physical_register_map':list(engine.r.PHY),
        'scope':'All nine independent natural logical registers, both decrement guards, arbitrary natural extra gap, arbitrary natural first spare and arbitrary finite remaining spare list, complete tape with blank exterior.',
        'proof_status':'Executable ordinary mathematical induction; no new proof-assistant endpoint.',
        'fuel_scope':'The 4000-step limit bounds symbolic proof construction only; it bounds neither counters nor concrete execution time.'}
    def save():
        result.update(cases=len(cases), seconds=time.monotonic()-started)
        build.dump(output,result)
    try:
        lemmas, blocks = engine.prove_blocks(table)
        result['blocks'] = blocks
        print('Four exact-table list induction schemas proved',flush=True)
        for i, site in enumerate(sites):
            for positive in ((False,True) if site[1] == 'CD' else (False,)):
                answer = engine.case(table,lemmas,site,positive)
                used.update(answer.pop('rows')); answer.pop('trace')
                cases.append({'site_index':i,'positive':positive,**answer})
                if len(cases)%1000 == 0:
                    save(); print('Proved',len(cases),'of',expected,'cases',flush=True)
        build.require(len(cases) == expected, 'Incomplete case coverage')
        build.require(used == set(table), 'Not every transition row was covered')
        case_path = output.with_name(output.stem+'_cases.json')
        build.dump(case_path,cases)
        result.update(status='UNIVERSAL_MATHEMATICAL_PASS',
            symbolic_steps=sum(c['symbolic_steps'] for c in cases),
            minimum_actual_steps=min(c['duration'][0] for c in cases),
            maximum_symbolic_steps=max(c['symbolic_steps'] for c in cases),
            used_rows=sorted(used), all_rows_used=True,
            cases_file=case_path.name, cases_sha256=digest(case_path))
        save()
        print(json.dumps({k:v for k,v in result.items() if k not in ('blocks','used_rows')},indent=2),flush=True)
        return result
    except Exception as exc:
        result.update(status='NOT_PROVED',site_index=locals().get('i'),site=locals().get('site'),
                      positive=locals().get('positive'),error=repr(exc))
        save(); raise

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path); ap.add_argument('sites',type=Path); ap.add_argument('output',type=Path)
    a = ap.parse_args(); prove(a.table,a.sites,a.output)
