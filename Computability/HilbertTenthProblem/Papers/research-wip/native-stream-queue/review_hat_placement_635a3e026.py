#!/usr/bin/env python3
"""Fresh, read-only Git/ZIP provenance collector; no supplied code executed."""
import argparse
import hashlib
import io
import json
import subprocess
import zipfile
from pathlib import Path

REPO = Path('/home/codex/.codex/worktrees/2a71/Proofs')
ARRIVAL = '26e036956381b07bb43de0187965f8dcdf9194fb'
PLACEMENT = '635a3e0266cec4426066aa96f0808720120b3323'
MERGE = 'b399cbd29592092e38af0a7c8d5427bfd3f8fff7'
ARCHIVE = 'docs/incoming/hat_randomness_frontier.zip'
HOST = 'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games'

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(commit, path):
    data = git('show', commit + ':' + path)
    return data, {'commit': commit, 'path': path, 'bytes': len(data),
                  'blob': git('rev-parse', commit + ':' + path).decode().strip(),
                  'sha256': sha(data)}

def span(data, first, last):
    lines = data.decode('utf-8').splitlines()
    if not 1 <= first <= last <= len(lines):
        raise ValueError('invalid read span')
    selected = ('\n'.join(lines[first - 1:last]) + '\n').encode()
    return {'first': first, 'last': last, 'lines': last-first+1,
            'normalized_utf8_sha256': sha(selected)}

def collect():
    parent = git('rev-parse', PLACEMENT + '^').decode().strip()
    raw, archive = blob(ARRIVAL, ARCHIVE)
    prior, prior_archive = blob(parent, ARCHIVE)
    if raw != prior:
        raise ValueError('archive changed between arrival and deletion parent')
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        members = {i.filename: z.read(i) for i in z.infolist() if not i.is_dir()}
    archive['members'] = [{'path': name, 'bytes': len(data), 'sha256': sha(data)}
                          for name, data in sorted(members.items())]
    statuses = [line.split('\t') for line in git('diff-tree', '--no-commit-id',
                 '--name-status', '-r', PLACEMENT).decode().splitlines()]
    if len(statuses) != 6 or sorted(s for s, p in statuses) != ['A']*5 + ['D']:
        raise ValueError('unexpected placement change set')
    changes = []
    matched = []
    for status, path in statuses:
        diff = git('diff', '--no-ext-diff', '--binary', parent, PLACEMENT, '--', path)
        item = {'status': status, 'path': path, 'diff_bytes': len(diff),
                'diff_sha256': sha(diff), 'diff_human_read': False}
        if status == 'A':
            data, item['after'] = blob(PLACEMENT, path)
            matches = [n for n, b in members.items() if b == data]
            if len(matches) != 1:
                raise ValueError('placed file lacks unique exact archive match')
            item['archive_member'] = matches[0]
            merged, item['at_merge'] = blob(MERGE, path)
            if merged != data:
                raise ValueError('placed bytes changed at merge')
            matched += matches
        else:
            if path != ARCHIVE:
                raise ValueError('unexpected deletion')
            item['before'] = prior_archive
        changes.append(item)
    unchanged = []
    read_spans = []
    part_headings = []
    for leaf in ['README.md', 'article.tex', 'article.pdf']:
        path = HOST + '/' + leaf
        before, bm = blob(parent, path)
        after, am = blob(PLACEMENT, path)
        merged, mm = blob(MERGE, path)
        if not before == after == merged:
            raise ValueError('host file changed')
        unchanged.append({'path': path, 'before': bm, 'after': am, 'at_merge': mm})
        if leaf == 'README.md':
            read_spans.append({'source': am, 'spans': [span(after, 1077, 1206)]})
        elif leaf == 'article.tex':
            part_headings = [{'line': i, 'text': line} for i, line in
                             enumerate(after.decode().splitlines(), 1)
                             if line.startswith('\\part{')]
    if len(part_headings) != 4:
        raise ValueError('unexpected part census')
    audit, audit_meta = blob(PLACEMENT, HOST + '/06-hat-randomness-SOURCE_AUDIT.txt')
    read_spans.append({'source': audit_meta, 'spans': [span(audit, 1, 86)]})
    rules, rule_meta = blob(PLACEMENT, 'docs/incoming/README.md')
    read_spans.append({'source': rule_meta, 'spans': [span(rules, 426, 450)]})
    previous_reviews = []
    expected = {
        'review_new_actions_26e036956.md': '55d864059205571c3eeab0d7522c72eaf7ea064c692fa9672dd10a7adc8b0a37',
        'review_hat_endpoint_26e036956.md': '06141d33d913bb6815cc0b9b99ce49b41a6065e45d36bb17d14d29914b42233c'}
    for name, pin in expected.items():
        path = Path('/tmp') / name
        data = path.read_bytes()
        if sha(data) != pin:
            raise ValueError('prior review pin changed')
        previous_reviews.append({'path': str(path), 'bytes': len(data), 'sha256': pin,
                                 'coverage': 'full review prose read; original source scope unchanged'})
    return {'schema': 'hat-placement-readonly-v1', 'arrival': ARRIVAL,
            'placement': PLACEMENT, 'parent': parent, 'merge': MERGE,
            'archive': archive, 'changes': changes, 'unchanged_host_files': unchanged,
            'unplaced_archive_members': sorted(set(members)-set(matched)),
            'literal_part_headings': part_headings, 'read_spans': read_spans,
            'previous_reviews': previous_reviews,
            'totals': {'archive_members': len(members), 'changed_paths': len(changes),
                       'exact_member_placements': len(matched), 'deleted_archives': 1,
                       'unchanged_host_files': len(unchanged),
                       'new_read_spans': 3, 'new_read_lines': 241},
            'scope': {'supplied_program_execution': False, 'supplied_program_import': False,
                      'supplied_program_human_read': False, 'builds': False,
                      'pdf_rendering': False, 'new_mathematical_proof_review': False,
                      'repository_mutation': False},
            'helper_sha256': sha(Path(__file__).read_bytes())}

def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    receipt = collect()
    if args.output:
        with args.output.open('x', encoding='utf-8') as out:
            json.dump(receipt, out, indent=2, sort_keys=True)
            out.write('\n')
    elif json.loads(args.expect.read_text()) != receipt:
        raise ValueError('receipt mismatch')
    print('PASS', json.dumps(receipt['totals'], sort_keys=True))

if __name__ == '__main__':
    main()
