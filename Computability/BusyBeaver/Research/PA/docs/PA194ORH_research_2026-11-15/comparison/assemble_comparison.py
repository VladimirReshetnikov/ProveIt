#!/usr/bin/env python3
"""Assemble current machine and delivery ledgers from explicit census results.

Historical semantic descriptions are attributed to the supplied loop-return
packet; literal identities and class membership are freshly recomputed by
census.py. This script does not infer arithmetic soundness from table data.
"""
from pathlib import Path
import argparse, collections, csv, hashlib, json, re

PIN = '43d9041f5571936c45c583f7f9d7f6eed9e0fd84'
NEW = [
 ('PA194GD', '1362fe8f264656e5b6d3e88666c0c88a34883c4d3cc5e9f2b4da9f9f6e8e595e', 'Explicit binder and offset diagonal', 'Generalize U(c,h), diagonal Gamma(d+x); independent operands; original distribution, no-push MP and sum guard.'),
 ('PA194GDH', 'e11b587cdb7d620adc9ce086467931f2d9db453f56231c5829e9f8c71c04eed1', 'Explicit binder and offset diagonal', 'GD calculus and no-push MP, with cache-only h=1 Shift.'),
 ('PA194GDHS', '7b69655c9115d226f23be4cd70303650f894a97d195c53139f72e1c937cdda58', 'Explicit binder and offset diagonal', 'GDH with symmetric cached-only comparator.'),
 ('PA194LCAX11GHF', '01c1b37ac3bbc51b2dfef22b8e42a6b3713ed720350269f819d82793e3f01bce', 'Loop reassociation with physical shortcuts', 'AX11GH plus loop-continuation reassociation and two guarded three-to-one shortcuts; logical source unchanged.'),
 ('PA194LCAX11GHSF', '6d03507fcc85825f81f7db5d02b0cb60e48f87c53be3dd0e4a8888d4922517a9', 'Loop reassociation with physical shortcuts', 'Symmetric AX11GHS plus loop reassociation and two guarded three-to-one shortcuts.'),
 ('PA194LCG', '5d8e4f5e03c72a8737b898c00a5fbd6e62476cc34a483613ed046d0dc113e84c', 'Loop reassociation with physical shortcuts', 'Loop-reassociated AX11GH with three shortcuts, including 190/1 using its unique incoming edge.'),
 ('PA194LCGS', 'ff084fd560d1b2792cda1c443ef522fe4953b1ff0677ad71100fb5e82d19b90b', 'Loop reassociation with physical shortcuts', 'Symmetric loop-reassociated AX11GHS with the same three guarded shortcuts.'),
 ('PA194AX11H_SF', '23fc656adc1afbe9e63f3a56df6e0c73a4f15a6d1493f2048aebaf00c9483ad2', 'History selector with physical shortcuts', 'Compatible history-selector and three-to-one acceleration composition on AX11H; direct factor-three bounded witness maps.'),
 ('PA194LC_AX11H_SF', 'e9c6864d7fb452dff86a38e561f39a2dac0ddb873369fdfa3c1e7a88edcac7bf', 'History selector with physical shortcuts', 'Same selector/acceleration composition on loop-reassociated AX11H.'),
]

def relpath(p):
    return p.split('/source/', 1)[-1]

def dump_csv(path, rows, fields):
    with path.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for row in rows:
            w.writerow({k: row.get(k, '') for k in fields})

def main(root):
    c = root / 'current_census'
    identities = json.loads((c/'identities.json').read_text())
    byhash = {x['normalized_sha256']: x for x in identities}
    frontier = json.loads((c/'frontier.json').read_text())
    occurrences = json.loads((c/'occurrences.json').read_text())
    corpus_meta = json.loads((root/'incoming_physical_corpus_meta.json').read_text())
    bysource = collections.defaultdict(list)
    for x in occurrences:
        bysource[x['source_sha256']].append(x)
    prior = json.loads((root/'prior_classes139.json').read_text())
    prior_named = json.loads((root/'prior_named74.json').read_text())
    annotation = {}
    for x in prior:
        y = byhash[x['normalized_sha256']]
        assert y['states'] == 194 and y['spanning']
        annotation[y['strict_graph']] = {
            'name': x['name'], 'family': x['family'], 'role': x['role'],
            'feature': x['feature'], 'proof_status': x['proof_status'],
            'named': x['named'], 'annotation_source': 'Supplied loop-return packet comparison/all_194_classes.json',
        }
    assert len(annotation) == 139
    named = []
    for x in prior_named:
        y = byhash[x['normalized_sha256']]
        named.append({
            'name': x['name'], 'family': x['family'], 'role': x['role'],
            'feature': x['feature'], 'proof_status': x['proof_status'],
            'duplicate_relationship': x['duplicate_relationship'],
            'strict_graph': y['strict_graph'], 'broad_graph': y['broad_graph'],
            'normalized_sha256': x['normalized_sha256'],
            'origin': 'Previously filed among the 93 packets',
        })
    prior_keys = set(annotation)
    for name, h, family, feature in NEW:
        found = [x for x in bysource[h] if x['states'] == 194]
        assert found, (name, h)
        y = byhash[found[0]['normalized_sha256']]
        assert y['strict_graph'] not in prior_keys
        x = {
            'name': name, 'family': family, 'role': 'Current incoming principal construction',
            'feature': feature,
            'proof_status': 'New written relative iPRA theorem; absolute claim imports revised AX11H written calibration; no new full Lean endpoint.',
            'named': True, 'annotation_source': 'Current archive top-level README, exact dense SHA-256 matched in fresh census',
        }
        assert y['strict_graph'] not in annotation, name
        annotation[y['strict_graph']] = x
        named.append({**x, 'strict_graph': y['strict_graph'], 'broad_graph': y['broad_graph'], 'normalized_sha256': y['normalized_sha256'], 'dense_sha256': h, 'origin': 'Current incoming archive', 'duplicate_relationship': 'Distinct from prior139 and other eight current named constructions; may also appear as another current packet research input.'})
    assert len(named) == 83 and len({x['strict_graph'] for x in named}) == 83
    all194 = []
    for x in frontier:
        if x['states'] != 194:
            continue
        g = x.get('strict_graph')
        paths = sorted({relpath(p['path']) + (p.get('json_pointer') or '') for p in x['sources']})
        a = annotation.get(g)
        if a is None:
            a = {
                'name': ('Unclassified research table ' + g[:12]) if x['spanning'] else 'Nonspanning diagnostic ' + x['normalized_sha256'][:12],
                'family': 'Research input or diagnostic',
                'role': 'Not identified as a principal consistency construction',
                'feature': 'Literal table retained in a historical or current research search; provenance locators supplied.',
                'proof_status': 'No consistency theorem inferred from this table census.',
                'named': False, 'annotation_source': 'Fresh structural census only',
            }
            for path in paths:
                m = re.search(r'/research/physical/inputs/corpus/([0-9a-f]{64})\.tm', path)
                if m and 'patches' in corpus_meta.get(m.group(1), {}):
                    meta = corpus_meta[m.group(1)]
                    labels = ','.join(meta['patches'])
                    a.update(name='Search composition '+labels+' of '+meta['base'][:12],
                        family='Syntactic physical-patch combinations',
                        role='Uncertified bounded-search input',
                        feature='Supplied corpus labels '+labels+' on base SHA-256 '+meta['base']+'. These combine loop-continuation (lc), accelerated-return (f), and selector (sel) patches; compatible row locations alone do not prove semantic compatibility.',
                        proof_status='The source explicitly makes no blanket correctness or calibration claim for these search inputs.',
                        annotation_source='Incoming comparison/new-designs packet research/physical/README.md and receipts/corpus_meta.json, matched by exact payload SHA-256',
                        research_base_sha256=meta['base'], research_patches=meta['patches'])
                    break
                m = re.search(r'/composites/machines/(PA194(?:LC_)?AX11H_SF)/selector\.native\.tm', path)
                if m:
                    a.update(name=m.group(1)+' selector intermediate',
                        family='History selector with physical shortcuts',
                        role='Intermediate in a principal reported composition',
                        feature='Selector-only intermediate before the final acceleration patch of '+m.group(1)+'.',
                        proof_status='Intermediate table in the supplied direct relative proof; not a separately named absolute calibration.',
                        annotation_source='Incoming comparison/new-designs packet composites/machines, exact source locator')
                    break
                m = re.search(r'/research/physical/inputs/closed/([^/]+)\.tm', path)
                if m:
                    a.update(name='Closed-macro research '+m.group(1),
                        family='Closed source-macro reassociation',
                        role='Uncertified bounded-search input',
                        feature='Source-CFG-preserving closed-macro reassociation retained after local folding; physical source correctness was not asserted.',
                        proof_status='Research input only; local folds and failed smaller-quotient searches do not calibrate the whole machine.',
                        annotation_source='Incoming comparison/new-designs packet research/physical/README.md, Closed-macro search candidates')
                    break
        all194.append({**a, 'states': 194, 'spanning': x['spanning'],
                       'strict_graph': g, 'broad_graph': x.get('broad_graph'),
                       'normalized_identities': x['normalized_identities'],
                       'occurrences': len(x['sources']), 'source_locators': paths,
                       'representative': 'current_census/representatives/' + ((g if g else 'disconnected_' + x['normalized_sha256']) + '.tm')})
    all194.sort(key=lambda x: (not x['named'], x['family'], x['name']))
    for x in named:
        a = next(z for z in all194 if z['strict_graph'] == x['strict_graph'])
        x['representative'] = a['representative']
        x['source_locators'] = a['source_locators']
    (root/'named_designs83.json').write_text(json.dumps(named, indent=2))
    (root/'frontier194_annotated.json').write_text(json.dumps(all194, indent=2))
    dump_csv(root/'named_designs83.csv', named, ['name','family','role','feature','proof_status','duplicate_relationship','strict_graph','broad_graph','normalized_sha256','representative','origin'])
    dump_csv(root/'frontier194_annotated.csv', all194, ['name','family','role','feature','proof_status','named','spanning','strict_graph','broad_graph','occurrences','representative'])
    summaries = dict(pin=PIN, deliveries=97, filed_deliveries=93, incoming_deliveries=4,
        prior_spanning194_recovered=len(prior_keys), current_spanning194=sum(x['spanning'] for x in all194),
        current_nonspanning194=sum(not x['spanning'] for x in all194),
        named_principal_and_supplementary_designs=83,
        current_named_incoming_designs=9,
        other_spanning194_classes=sum(x['spanning'] and not x['named'] for x in all194),
        new_spanning194_since_prior139=sum(x['spanning'] and x['strict_graph'] not in prior_keys for x in all194),
        proof_status='Names and mathematical claims are attributed to packets, not certified by graph isomorphism.')
    (root/'comparison_summary.json').write_text(json.dumps(summaries, indent=2))
    print(json.dumps(summaries, indent=2))

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    main(ap.parse_args().root)
