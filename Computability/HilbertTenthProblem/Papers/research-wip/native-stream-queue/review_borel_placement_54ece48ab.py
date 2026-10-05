#!/usr/bin/env python3
"""Fresh read-only Git/ZIP placement authentication; never runs delivery code."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

COMMIT = '54ece48ab0b52e823bd66814b38c330b9198224b'
MERGE = '23eee75ef157b65c897d3364d052bd43a4b50ff3'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
SPECS = [
 ('Borel_Conjugacy_Divisibility_Threshold.zip', '62846e17a', 'review_new_borel_62846e17a', '24-borel-conjugacy', 'pma:bct:'),
 ('glazer_proveit_support_complexity.zip', '7be14aa84', 'review_new_support_complexity_fb9f5884b', '25-support-complexity', 'pma:spc:'),
 ('Borel_Flows_Glazer_ProveIt.zip', 'fb9f5884b', 'review_new_borel_flows_fb9f5884b', '26-borel-flows', 'pma:bfl:'),
 ('Two_Derivations_Borel_Conjugacy.zip', '78528873b', 'review_two_derivations_78528873b', '27-two-derivations', 'pma:tdv:')]
NOTE_NAMES = ['25-support-complexity-sources.md', '26-borel-flows-CLAIM_LEDGER.md',
              '26-borel-flows-SOURCES.md', '27-two-derivations-SOURCE_AUDIT.md']

def check(test, message):
    if not test:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def record(data):
    return {'bytes': len(data), 'sha256': digest(data)}

def span(data, first, last, mode):
    lines = data.splitlines(keepends=True)
    check(1 <= first <= last <= len(lines), 'read span out of range')
    return {'first_line': first, 'last_line': last, 'mode': mode,
            **record(b''.join(lines[first-1:last]))}

def main(args):
    def git(*parts):
        return subprocess.check_output(['git', '-C', args.root, *parts])
    def resolve(ref):
        return git('rev-parse', ref).decode().strip()
    def file_record(ref, path):
        data = git('show', ref+':'+path)
        return data, {'commit': resolve(ref), 'path': path,
                      'blob': resolve(ref+':'+path), **record(data)}
    parent = resolve(COMMIT+'^')
    parents = git('show', '-s', '--format=%P', MERGE).decode().split()
    check(COMMIT in parents, 'placement not a direct merge parent')
    change_bytes = git('diff-tree', '--no-commit-id', '--name-status', '-r', COMMIT)
    changes = [dict(zip(('status', 'path'), x.split('\t'))) for x in change_bytes.decode().splitlines()]
    added = [r['path'] for r in changes if r['status'] == 'A']
    deleted = [r['path'] for r in changes if r['status'] == 'D']
    check(len(changes) == 21 and len(added) == 17 and len(deleted) == 4, 'changed-path census')
    check(set(deleted) == {'docs/incoming/'+s[0] for s in SPECS}, 'deleted archive paths')
    check(all(p.startswith(HOST) for p in added), 'unexpected placement')
    additions = {p: file_record(COMMIT, p) for p in added}
    archives, placements, prior_reviews, delivery_readmes = [], [], [], []
    source_member_reads = []
    for name, arrival_short, prior_stem, prefix, label_prefix in SPECS:
        path = 'docs/incoming/'+name
        data, rec = file_record(parent, path)
        arrival, ar = file_record(arrival_short, path)
        check(data == arrival, 'arrival/retirement archive mismatch')
        check(not git('ls-tree', '-r', '--name-only', COMMIT, path).strip(), 'archive not retired')
        z = zipfile.ZipFile(io.BytesIO(data))
        members = {}
        inventory = []
        for inf in z.infolist():
            if inf.is_dir():
                continue
            body = z.read(inf.filename)
            check(inf.filename not in members, 'duplicate ZIP name')
            members[inf.filename] = body
            inventory.append({'path': inf.filename, **record(body), 'crc32': f'{inf.CRC:08x}',
                              'compressed_bytes': inf.compress_size, 'coverage': 'hash only in this placement review'})
        manifests = [p for p in members if Path(p).name in ('SHA256SUMS', 'MANIFEST.sha256')]
        check(len(manifests) == 1, 'manifest count')
        manifest = manifests[0]
        checksum_rows = []
        for line in members[manifest].decode().splitlines():
            match = re.fullmatch(r'([0-9a-fA-F]{64})\s+\*?(.+)', line)
            check(match is not None, 'unparsed checksum line')
            sha, relative = match.groups()
            candidates = [p for p in members if p == relative or p == str(Path(manifest).parent/relative)]
            check(len(candidates) == 1, 'ambiguous checksum member')
            member = candidates[0]
            check(digest(members[member]) == sha.lower(), 'checksum mismatch')
            checksum_rows.append({'path': member, 'sha256': sha.lower()})
        check({x['path'] for x in checksum_rows} == set(members)-{manifest}, 'manifest not exhaustive')
        for item in inventory:
            base = Path(item['path']).name
            if base == 'README.md':
                body = members[item['path']]
                item['coverage'] = 'full guide read this review'
                item['read_spans'] = [span(body, 1, len(body.splitlines()), 'full delivered guide')]
                delivery_readmes.append((name, body.decode()))
            if item['path'] == manifest:
                item['coverage'] = 'all checksum records parsed and independently checked'
        placed_here = []
        for p, (body, dst) in additions.items():
            if prefix not in p:
                continue
            matches = [member for member, val in members.items() if val == body]
            check(len(matches) == 1, 'placement missing or ambiguous')
            member = matches[0]
            entry = {**dst, 'archive_path': path, 'member': member, 'byte_identical': True,
                     'carriage_return_bytes': body.count(b'\r')}
            if p.removeprefix(HOST) in NOTE_NAMES:
                entry['read_spans'] = [span(body, 1, len(body.splitlines()), 'full placed provenance/status note')]
                inv = next(i for i in inventory if i['path'] == member)
                inv['coverage'] = 'full text read via byte-identical placed provenance/status note'
                inv['read_spans'] = entry['read_spans']
            else:
                entry['coverage'] = 'byte authentication only; no delivered code executed or evidence replayed'
            placements.append(entry)
            placed_here.append(member)
        unplaced = set(members)-set(placed_here)
        check(len(unplaced) == 4 and sum(p.endswith('.tex') for p in unplaced) == 1
              and sum(p.endswith('.pdf') for p in unplaced) == 1
              and any(Path(p).name == 'README.md' for p in unplaced)
              and manifest in unplaced, 'unexpected unplaced payload')
        # One explicitly inherited editorial issue; direct source locator only.
        if prefix == '26-borel-flows':
            tex = next(p for p in members if p.endswith('/borel_flows.tex'))
            body = members[tex]
            check(b'Theorem~\nef{thm:timeoneexact}' in body, 'inherited broken reference not found')
            source_member_reads.append({'archive_path': path, 'member': tex,
                 **record(body), 'read_spans': [span(body, 160, 172, 'editorial issue locator only')]})
        archives.append({**rec, 'arrival': ar, 'arrival_bytes_equal': True,
                         'absent_at_child': True, 'members': inventory,
                         'manifest': manifest, 'manifest_entries': checksum_rows,
                         'placed_members': sorted(placed_here),
                         'not_placed_members': sorted(set(members)-set(placed_here)),
                         'planned_label_prefix': label_prefix})
        old = {}
        for ext in ('md', 'json', 'py'):
            prior_data, prior_rec = file_record(COMMIT, WIP+prior_stem+'.'+ext)
            if ext == 'md':
                prior_rec['read_spans'] = [span(prior_data, 1, len(prior_data.splitlines()), 'full prior review note; inherited scope, no manuscript rereview')]
                check(Path(args.root, WIP+prior_stem+'.md').read_bytes() == prior_data, 'read local prior MD differs from immutable pin')
            elif ext == 'json':
                json.loads(prior_data)
                prior_rec['coverage'] = 'valid inert JSON and byte pin only; prior checks not replayed'
            else:
                prior_rec['coverage'] = 'hash only; not executed/imported/copied'
            old[ext] = prior_rec
        prior_reviews.append(old)
    check(len(placements) == 17 and len({p['path'] for p in placements}) == 17, 'complete placement map')
    total = sum(p['bytes'] for p in placements)
    check(total == 131536 and all(p['carriage_return_bytes'] == 0 for p in placements), 'delivery byte census')
    check([len(a['members']) for a in archives] == [6,8,9,10], 'archive member totals')
    check([len(a['manifest_entries']) for a in archives] == [5,7,8,9], 'manifest totals')
    hosts = []
    for leaf in ('README.md', 'article.tex', 'article.pdf'):
        body, rec = file_record(COMMIT, HOST+leaf)
        before, before_rec = file_record(parent, HOST+leaf)
        check(body == before, 'host file changed')
        row = {**rec, 'parent': before_rec, 'unchanged': True}
        if leaf == 'README.md':
            row['read_spans'] = [span(body, 1, 110, 'host guide introduction, source table and placement history')]
            check(b'Parts XVIII' not in body and b'Part XXI' not in body, 'unexpected new guide part')
        elif leaf == 'article.tex':
            lines = body.splitlines(keepends=True)
            parts = [{'line': i+1, 'text': line.decode().rstrip('\n'), **record(line)}
                     for i, line in enumerate(lines) if re.match(rb'\\part\{', line)]
            check(len(parts) == 17, 'actual host part count')
            row['part_heading_locators_read'] = parts
            row['new_prefix_occurrences'] = {s[4]: body.count(s[4].encode()) for s in SPECS}
            check(not any(row['new_prefix_occurrences'].values()), 'new labels already integrated')
            row['coverage'] = '17 one-line part heading locators only; no host manuscript proof rereview'
        else:
            row['coverage'] = 'hash only; no render, content read or build'
        hosts.append(row)
    instructions = []
    for path, first, last in [('Algebra/SurrealNumbers/AGENTS.md', 1, None), ('docs/incoming/README.md', 426, 438)]:
        data, rec = file_record(COMMIT, path)
        last = last or len(data.splitlines())
        rec['read_spans'] = [span(data, first, last, 'applicable instructions')]
        instructions.append(rec)
    full_diff = git('diff', '--no-ext-diff', '--no-renames', '--no-color', parent, COMMIT, '--')
    note_paths = [HOST+n for n in NOTE_NAMES]
    notes_diff = git('diff', '--no-ext-diff', '--no-renames', '--no-color', '--unified=0', parent, COMMIT, '--', *note_paths)
    message = git('show', '-s', '--format=%B', COMMIT)
    result = {'schema': 'borel-placement-independent-review-v1',
              'helper_sha256': digest(Path(__file__).read_bytes()), 'commit': COMMIT,
              'parent': parent, 'merge': MERGE, 'merge_parents': parents,
              'commit_message': {**record(message), 'coverage': 'full read'},
              'changed_paths': changes, 'changed_path_output': record(change_bytes),
              'full_diff': {**record(full_diff), 'coverage': 'hash only, not full code/data diff read'},
              'notes_diff': {**record(notes_diff), 'coverage': 'all added note text read in full; diff has no old text'},
              'archives': archives, 'placements': placements, 'host_files': hosts,
              'instructions': instructions, 'source_member_reads': source_member_reads,
              'prior_reviews': prior_reviews,
              'totals': {'changed_paths': 21, 'added_files': 17, 'retired_archives': 4,
                         'regular_archive_members': 33, 'manifest_entries_verified': 29,
                         'placed_bytes': total, 'host_parts': 17,
                         'placed_note_lines_read': sum(len(additions[p][0].splitlines()) for p in note_paths),
                         'longest_changed_placement_path': max(map(len, added))},
              'result': 'PASS: exact ancillary placements; host publication unchanged',
              'limits': ['No delivered program or predecessor helper executed/imported.',
                         'No manuscript theorem rereview, external source verification, or build.',
                         'No PDF read/render and no new compiler or operation count claim.',
                         'Prior review results retained with their original hypotheses and encoding limits.']}
    if args.print_guides:
        for name, body in delivery_readmes:
            print('\nARCHIVE GUIDE:', name, '\n'+body)
        for source in source_member_reads:
            a = next(a for a in archives if a['path'] == source['archive_path'])
            z = zipfile.ZipFile(io.BytesIO(git('show', parent+':'+a['path'])))
            print('\nSOURCE LOCATOR:', source['member'])
            for i, line in enumerate(z.read(source['member']).decode().splitlines(), 1):
                if 160 <= i <= 172:
                    print(i, line)
    encoded = (json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True)+'\n').encode()
    if args.write:
        Path(args.write).write_bytes(encoded)
    if args.expect:
        check(Path(args.expect).read_bytes() == encoded, 'receipt replay mismatch')
    print(json.dumps(result['totals'], sort_keys=True))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True)
    parser.add_argument('--write')
    parser.add_argument('--expect')
    parser.add_argument('--print-guides', action='store_true')
    main(parser.parse_args())
