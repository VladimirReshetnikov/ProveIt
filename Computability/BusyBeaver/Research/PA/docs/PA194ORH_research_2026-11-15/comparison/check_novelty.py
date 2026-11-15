#!/usr/bin/env python3
"""Compare a complete literal table with the pinned current 193/194 corpus.

Default checks every frozen representative's content identity, then uses its
freshly computed canonical signature. --recompute regenerates every canonical
form. Any signature equality is checked by exact canonical tuple equality.
Different signatures rigorously imply different tuples; collision risk cannot
create a false novelty verdict. The frozen-signature correctness is part of
the reproducible census computation, not a machine-behavior theorem.
"""
from pathlib import Path
import argparse, hashlib, json
import census

def run(path, root, recompute=False):
    data = census.parse_text(path.read_bytes())
    if data is None:
        raise ValueError('Candidate is not a complete numeric binary L/R one-halt table')
    strict = census.canonical_form(data)
    broad = census.canonical_form(data, broad=True)
    if strict is None:
        raise ValueError('Candidate has no spanning control root; use a disconnected-graph comparator')
    sh, bh = census.fingerprint(strict), census.fingerprint(broad)
    records = json.loads((root/'current_census/frontier.json').read_text())
    checked = 0
    matches = []
    disconnected = 0
    for x in records:
        if x['states'] != len(data[1]):
            continue
        g = x.get('strict_graph')
        p = root/'current_census/representatives'/((g if g else 'disconnected_'+x['normalized_sha256'])+'.tm')
        frozen = p.read_bytes()
        assert hashlib.sha256(frozen).hexdigest() == x['normalized_sha256'], p
        old = census.parse_text(frozen)
        assert old is not None and len(old[1]) == x['states']
        if not x['spanning']:
            assert census.canonical_form(old) is None
            disconnected += 1
            continue
        checked += 1
        os, ob = x['strict_graph'], x['broad_graph']
        if recompute:
            os = census.fingerprint(census.canonical_form(old))
            ob = census.fingerprint(census.canonical_form(old, broad=True))
            assert os == x['strict_graph'] and ob == x['broad_graph'], p
        if bh == ob:
            other = census.canonical_form(old, broad=True)
            if broad == other:
                matches.append({'representative': str(p), 'strict_match': strict == census.canonical_form(old), 'broad_match': True,
                    'source_locators': sorted({z['path'].split('/source/',1)[-1] for z in x['sources']})})
    result = {'candidate': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'working_states':len(data[1]), 'spanning_from_zero': (0 in data[1] and census.rooted_form(data,0)[1] == len(data[1])),
        'strict_graph':sh, 'broad_graph':bh, 'compared_spanning_classes':checked,
        'excluded_nonspanning_diagnostics':disconnected, 'recomputed_all_forms':recompute,
        'matches':matches, 'structurally_new':not matches,
        'scope':'State renaming, all spanning roots, reflection, global bit exchange, and ignored terminal actions. No behavioral or arithmetic-calibration claim.'}
    return result

if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--recompute',action='store_true')
    ap.add_argument('--output',type=Path)
    a=ap.parse_args();r=run(a.candidate,a.root,a.recompute)
    s=json.dumps(r,indent=2)
    if a.output:a.output.write_text(s+'\n')
    print(s)
