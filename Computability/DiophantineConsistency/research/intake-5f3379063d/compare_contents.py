#!/usr/bin/env python3
"""Compare exact content hashes with selected prior inventories and sealed research."""
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INVENTORIES = ['research/incoming-e13c748234/INVENTORY.json', 'research/intake-45b399ec51/INVENTORY.json']
PACKETS = ['ten-positive-saturated-pell', 'ten-positive-reused-b-weight',
           'ten-positive-uncentered-b-weight', 'saturated-direct-carrier-cse',
           'round14-pair-guard-compression', 'round14-pair-guard-projections']


def need(condition, label):
    if not condition:
        raise ValueError(label)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    oldmembers, oldarchives, research = defaultdict(list), defaultdict(list), defaultdict(list)
    pins = {}
    for name in INVENTORIES:
        path = ROOT / name;pins[name] = digest(path);data = json.loads(path.read_text())['archives']
        data = data.items() if isinstance(data, dict) else [(a['archive'], a) for a in data]
        for archive, record in data:
            oldarchives[record['sha256']].append(name + '::' + archive)
            for member in record['members']:
                oldmembers[member['sha256']].append(name + '::' + archive + '::' + member.get('name', member.get('member')))
    for packet in PACKETS:
        folder = ROOT / 'research' / packet;manifest = folder / 'MANIFEST.json'
        pins[str(manifest.relative_to(ROOT))] = digest(manifest)
        files = json.loads(manifest.read_text())['files']
        need(set(files) == {str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file() and p != manifest}, 'closed selected baseline')
        for name, h in files.items():
            path = folder / name;need(digest(path) == h, 'whole selected baseline member')
            research[h].append(str(path.relative_to(ROOT)))
    incoming = json.loads((HERE / 'INVENTORY.json').read_text())
    summaries, refs = [], {}
    for archive in incoming['archives']:
        prior, accepted, nested, novel = [], [], [], []
        for member in archive['members']:
            h = member['sha256'];references = dict(prior_members=oldmembers.get(h, []),
                selected_sealed_research=research.get(h, []), exact_old_archives=oldarchives.get(h, []))
            if any(references.values()):refs[h] = references
            if references['prior_members']:prior.append(member['name'])
            if references['selected_sealed_research']:accepted.append(member['name'])
            if references['exact_old_archives']:nested.append(member['name'])
            if not any(references.values()):novel.append(member['name'])
        summaries.append(dict(archive=archive['path'], exact_prior_archive_matches=oldarchives.get(archive['sha256'], []),
            member_count=archive['member_count'], prior_member_byte_matches=prior,
            selected_sealed_research_byte_matches=accepted, whole_old_archive_members=nested,
            content_not_found_in_selected_baselines=novel))
    result = dict(scope='Exact bytes only, relative to the explicitly selected snapshots; no semantic equivalence or global novelty inferred.',
                  baseline_input_sha256=pins, incoming_inventory_sha256=digest(HERE/'INVENTORY.json'),
                  references_by_sha256=refs, archives=summaries)
    text = json.dumps(result, indent=2, sort_keys=True) + '\n';path = HERE/'CONTENT_COMPARISON.json'
    if path.exists():need(path.read_text() == text, 'refuse changed comparison overwrite')
    else:path.write_text(text)
    print(json.dumps([dict(archive=Path(a['archive']).name, members=a['member_count'],
        old_member_matches=len(a['prior_member_byte_matches']), sealed_research_matches=len(a['selected_sealed_research_byte_matches']),
        old_whole_archives=len(a['whole_old_archive_members']), unmatched_content=len(a['content_not_found_in_selected_baselines'])) for a in summaries], indent=2))


if __name__ == '__main__':
    main()
