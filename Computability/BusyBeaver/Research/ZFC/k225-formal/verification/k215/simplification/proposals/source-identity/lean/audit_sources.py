#!/usr/bin/env python3
"""Owned, read-only source audit. Never imports or runs repository code."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
BASE = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
SELECTED = {
    'KLowerRel.lean': ['Tag', 'tmem', 'sh', 'relT', 'Shows', 'shows_scons', 'sat_relT', 'sat_top'],
    'WFRelativization.lean': ['translate', 'liftEnv', 'liftEnv_scons', 'sat_guard', 'sat_translate',
        'sat_translate_of_wf', 'sat_translate_scons', 'sat_translate_matrix',
        'sat_translate_relOf', 'equalityFree_translate'],
    'ConstructibleReflect.lean': ['CSat', 'consSlot', 'relT', 'nsat_relT'],
    'ConstructibleZF.lean': ['csat_rename', 'sat_sub'],
    'KEndpoint.lean': ['c222_of_zf_refutation'],
    'KQ1Replacement.lean': ['replacementChoiceForm', 'quotient_replacement'],
    'KQ1ZF.lean': ['zfAxioms', 'zf_consistent'],
}
CHAINS = [
    ['KEndpoint215', 'KEndpoint', 'KLowerQHyp', 'KLowerEqv', 'KLowerTag', 'KLowerRel'],
    ['KEndpoint215', 'KEndpoint', 'KLowerQHyp', 'KQ1ZF', 'WFModelCore', 'WFRelativization'],
]
TARGET_RANGES = [
    ('KLowerRel.lean', 'relT', 28, 36, False),
    ('KLowerRel.lean', 'sat_relT', 54, 74, False),
    ('WFRelativization.lean', 'translate', 28, 36, False),
    ('WFRelativization.lean', 'sat_translate', 63, 112, False),
    ('KLowerRel.lean', 'Shows', 39, 40, True),
    ('KLowerRel.lean', 'shows_scons', 45, 52, True),
]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, help='Optional read-only checkout to compare exact source bytes')
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    packet = json.loads((ROOT / 'source_snapshots.json').read_text())
    assert packet['pin'] == PIN
    index = {s['path']: s for s in packet['sources']}
    assert len(index) == len(packet['sources']), 'Duplicate paths'
    files = []
    for path, source in index.items():
        content = source['content'].encode()
        expected = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
        assert expected == source['sha'], (path, 'Git blob SHA mismatch')
        assert source['ref'] == PIN
        assert (ROOT / 'sources' / path).read_bytes() == content
        if args.repo:
            assert (args.repo / path).read_bytes() == content, (path, 'Checkout differs from frozen source')
        files.append({'path': path, 'git_blob_sha1': expected,
            'sha256': hashlib.sha256(content).hexdigest(), 'bytes': len(content),
            'lines': len(source['content'].splitlines()), 'url': source['display_url']})
    locations = []
    for filename, names in SELECTED.items():
        source = index[BASE + filename]
        lines = source['content'].splitlines()
        for name in names:
            hits = [i for i, line in enumerate(lines, 1)
                    if re.match(r'^(?:def|theorem|abbrev|structure)\s+' + re.escape(name) + r'\b', line)]
            assert len(hits) == 1, (filename, name, hits)
            locations.append({'file': filename, 'declaration': name, 'line': hits[0],
                'url': source['display_url'] + '#L' + str(hits[0])})
    for chain in CHAINS:
        for source, target in zip(chain, chain[1:]):
            text = index[BASE + source + '.lean']['content']
            assert re.search(r'^import BusyBeaver\.ZFC\.' + target + r'\s*$', text, re.M), (source, target)
    endpoint = index[BASE + 'KEndpoint.lean']['content']
    replacement = index[BASE + 'KQ1Replacement.lean']['content']
    assert 'fullSeed_direct_of_derivable' in endpoint
    assert 'KSeedDirect222' in endpoint
    assert 'KQ1Model.translate phi' in replacement
    target_ranges = []
    for filename, name, first, last, optional in TARGET_RANGES:
        lines = index[BASE + filename]['content'].splitlines()
        assert re.match(r'^(?:def|theorem)\s+' + re.escape(name) + r'\b', lines[first - 1])
        assert lines[last - 1].strip() and not lines[last].strip()
        target_ranges.append({'file': filename, 'declaration': name,
            'first_line': first, 'last_line': last, 'physical_lines': last - first + 1,
            'optional_additional_target': optional})
    draft_files = []
    for name in ['GuardedSubtype.lean', 'GuardedSubtypeAdapters.lean']:
        content = (ROOT / name).read_bytes()
        draft_files.append({'file': name, 'physical_lines': len(content.splitlines()),
            'bytes': len(content), 'sha256': hashlib.sha256(content).hexdigest()})
    cost = {'metric': 'physical lines, including blank lines and comments',
        'old_declaration_ranges': target_ranges,
        'old_translators_and_main_proofs': sum(x['physical_lines'] for x in target_ranges
            if not x['optional_additional_target']),
        'old_target_including_tagged_environment_helpers': sum(x['physical_lines'] for x in target_ranges),
        'complete_uncompiled_draft_files': draft_files,
        'delivered_draft_total': sum(x['physical_lines'] for x in draft_files),
        'interpretation': 'Addition-only comparison experiment, not a deletion patch. '
            'The core alone exceeds the direct old target; public compatibility wrappers still required.'}
    result = {'pin': PIN, 'validation': 'source/data audit only; Lean never run',
        'sources_verified': len(files), 'files': files, 'declarations': locations,
        'verified_import_path_witnesses': CHAINS,
        'maintained_source_cost': cost,
        'scope': 'Selected lower-chain source slices; not a complete endpoint closure census',
        'facts': {'direct_full_seed_in_endpoint': True,
            'legacy_raw_replacement_still_in_production': True,
            'named_constructible_translation_excluded_from_reuse_claim': True,
            'kernel_check_performed': False, 'endpoint_build_performed': False,
            'closure_savings_measured': False}}
    rendered = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(rendered)
    else:
        print(rendered)

if __name__ == '__main__':
    main()
