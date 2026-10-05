#!/usr/bin/env python3
"""Fresh read-only provenance checker; supplied scripts are bytes, never code.

Run this new checker only before its review is frozen. It reads immutable Git
objects, authenticates ZIP members/internal hashes and prior recorded spans,
and writes a new receipt exclusively. It performs no build or source replay.
"""
import argparse
import hashlib
import io
import json
import pathlib
import re
import stat
import subprocess
import zipfile

PLACEMENT = '6571ee1afb1984a21aeddd84275c3a7cc2a28e80'
PARENT = '5b3757752049fb889e301d12e7cde8aae862e30a'
ARRIVAL = 'd7cf7d5547a50a6cf372f2cfaad96e950a68c03a'
ZIP = 'docs/incoming/Beyond_Ord_Research_Package.zip'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/'
PRIOR = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_beyond_ord_package_d7cf7d554'
MAPPING = {
    '36-horizons-SOURCE_AUDIT.txt': 'Beyond_Ord/SOURCE_AUDIT.txt',
    'code/36-horizons-build.sh': 'Beyond_Ord/build.sh',
    'code/36-horizons-notation_demo.py': 'Beyond_Ord/code/notation_demo.py',
    'data/36-horizons-DOCUMENT_CHECKS.json': 'Beyond_Ord/DOCUMENT_CHECKS.json',
    'data/36-horizons-verification.json': 'Beyond_Ord/code/verification.json',
}
READS = {
    'Beyond_Ord/README.txt': [(1, 67)],
    'Beyond_Ord/code/README.md': [(1, 128)],
    'Beyond_Ord/SOURCE_AUDIT.txt': [(1, 70)],
    'Beyond_Ord/DOCUMENT_CHECKS.json': [(1, 70)],
    'Beyond_Ord/code/verification.json': [(1, 55)],
    'Beyond_Ord/build.sh': [(1, 5)],
    'Beyond_Ord/code/notation_demo.py': [(1, 420)],
    'Beyond_Ord/beyond_ord.tex': [(720, 780), (939, 1093)],
}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def pin(data):
    return {'bytes': len(data), 'sha256': sha(data), 'git_blob_sha1': blob(data)}

def spans(data, ranges):
    lines = data.decode('utf-8').splitlines()
    answer = []
    for first, last in ranges:
        require(1 <= first <= last <= len(lines), 'bad read span')
        selected = ('\n'.join(lines[first-1:last]) + '\n').encode()
        answer.append({'first': first, 'last': last, 'lines': last-first+1,
                       'normalized_utf8_sha256': sha(selected)})
    return answer

def run(root):
    def git(*args):
        return subprocess.check_output(['git', '-C', str(root), *args])
    def obj(commit, path):
        return git('show', commit + ':' + path)
    def record(commit, path):
        data = obj(commit, path)
        answer = {'commit': commit, 'path': path, **pin(data)}
        require(git('rev-parse', commit + ':' + path).decode().strip() == answer['git_blob_sha1'], 'Git blob mismatch')
        return answer

    require(git('rev-parse', PLACEMENT + '^').decode().strip() == PARENT, 'parent')
    raw_status = git('diff-tree', '--no-commit-id', '--name-status', '-r', PARENT, PLACEMENT)
    statuses = [line.split('\t') for line in raw_status.decode().splitlines()]
    expected = sorted([['A', HOST+p] for p in MAPPING] + [['D', ZIP]])
    require(sorted(statuses) == expected, 'unexpected changed paths')
    archive_data = obj(ARRIVAL, ZIP)
    require(sha(archive_data) == 'a598178e496417cdaf982e387d72aad9ca954778296ea70c51e684f69d3acd12', 'arrival archive pin')
    require(obj(PARENT, ZIP) == archive_data, 'retired ZIP differs from arrival')
    require(not git('ls-tree', PLACEMENT, '--', ZIP), 'ZIP not retired')
    zf = zipfile.ZipFile(io.BytesIO(archive_data))
    require(zf.testzip() is None, 'ZIP CRC failure')
    names = [i.filename for i in zf.infolist()]
    require(len(names) == len(set(names)), 'duplicate ZIP name')
    members = []
    payloads = {}
    for info in zf.infolist():
        p = pathlib.PurePosixPath(info.filename)
        require(not p.is_absolute() and '..' not in p.parts, 'unsafe member')
        mode = info.external_attr >> 16
        require(not stat.S_ISLNK(mode), 'symlink ZIP member')
        if info.is_dir():
            continue
        data = zf.read(info)
        payloads[info.filename] = data
        member = {'path': info.filename, **pin(data), 'crc32': format(info.CRC, '08x'),
                  'compressed_bytes': info.compress_size, 'read_spans': spans(data, READS[info.filename]) if info.filename in READS else []}
        member['coverage'] = ('inert text read in specified spans' if member['read_spans'] else 'PDF bytes only; not rendered or read')
        members.append(member)
    require(len(members) == 9, 'member census')
    document = json.loads(payloads['Beyond_Ord/DOCUMENT_CHECKS.json'])
    internal = []
    for path, digest in document['sha256'].items():
        full = 'Beyond_Ord/' + path
        require(sha(payloads[full]) == digest, 'internal manifest ' + full)
        internal.append({'path': full, 'sha256': digest, 'match': True})
    require(len(internal) == 4, 'internal hash census')

    placed = []
    for target, source in MAPPING.items():
        path = HOST + target
        data = obj(PLACEMENT, path)
        require(data == payloads[source], 'placed bytes ' + target)
        require(b'\r' not in data, 'unexpected CR')
        diff = git('diff', '--no-ext-diff', '--no-color', '--no-renames', '--unified=3', PARENT, PLACEMENT, '--', path)
        placed.append({**record(PLACEMENT, path), 'source_member': source, 'byte_identical': True,
                       'read_spans': spans(data, [(1, len(data.decode().splitlines()))]),
                       'complete_read_diff': {**pin(diff), 'lines': len(diff.splitlines())}})
    require(sum(p['bytes'] for p in placed) == 24944, 'placed byte total')
    host = []
    forbidden = ['swo:hn:', 'swo:part:horizons', 'swo:xvii:', '36-horizons']
    for name in ['README.md', 'article.tex', 'article.pdf']:
        path = HOST + name
        data = obj(PLACEMENT, path)
        require(obj(PARENT, path) == data, 'host changed')
        rec = {**record(PLACEMENT, path), 'parent_blob': git('rev-parse', PARENT+':'+path).decode().strip(), 'unchanged_from_parent': True}
        if name.endswith(('.md', '.tex')):
            text = data.decode()
            rec['source36_token_counts'] = {s: text.count(s) for s in forbidden}
            require(not any(rec['source36_token_counts'].values()), 'unexpected source36 token')
            rec['read_spans'] = spans(data, [(1, 100)]) if name == 'README.md' else []
            if name == 'article.tex':
                rec['part_lines'] = [{'line': n, 'text': line} for n, line in enumerate(text.splitlines(), 1) if re.match(r'\\part(?:\[|\{)', line)]
                rec['coverage'] = 'metadata and exact source36-token scan only; no host body re-review'
        else:
            rec['coverage'] = 'bytes only; not rendered/read/built'
        host.append(rec)

    prior = {suffix: record(PLACEMENT, PRIOR+'.'+suffix) for suffix in ['md', 'json', 'py']}
    prior['md']['read_spans'] = spans(obj(PLACEMENT, PRIOR+'.md'), [(1, len(obj(PLACEMENT, PRIOR+'.md').decode().splitlines()))])
    prior['py']['coverage'] = 'hash only; not executed/imported'
    old = json.loads(obj(PLACEMENT, PRIOR+'.json'))
    require(prior['py']['sha256'] == old['reviewer_helper_sha256'], 'prior helper pin')
    old_archive = old['archives'][0]
    require(old_archive['sha256'] == sha(archive_data), 'prior ZIP pin')
    verified_spans = 0
    for old_member in old_archive['members']:
        data = payloads[old_member['path']]
        require(old_member['sha256'] == sha(data) and old_member['bytes'] == len(data), 'prior member pin')
        for span in old_member['read_spans']:
            require(spans(data, [(span['first'], span['last'])])[0] == span, 'prior recorded span')
            verified_spans += 1
    require(verified_spans == 17, 'prior span census')
    prior['scope'] = old['scope']
    prior['recorded_archive_spans_reauthenticated'] = verified_spans
    prior['recorded_archive_lines_reauthenticated'] = old['totals']['archive_read_lines']
    prior['inherited_article_spans'] = next(x['read_spans'] for x in old_archive['members'] if x['path'].endswith('beyond_ord.tex'))
    prior['human_coverage_warning'] = 'Prior recorded spans authenticated as bytes, not all re-read in this placement review.'
    message = git('show', '-s', '--format=%B', PLACEMENT)
    full_diff = git('diff', '--no-ext-diff', '--no-color', '--no-renames', '--binary', '--unified=3', PARENT, PLACEMENT, '--')
    text_diff = git('diff', '--no-ext-diff', '--no-color', '--no-renames', '--unified=3', PARENT, PLACEMENT, '--', *[HOST+p for p in MAPPING])
    return {
        'schema': 'beyond-ord-horizons-placement-review-v1',
        'placement': PLACEMENT, 'parent': PARENT, 'arrival': ARRIVAL,
        'commit_message': {**pin(message), 'read_spans': spans(message, [(1, len(message.decode().splitlines()))])},
        'status': statuses, 'status_bytes': pin(raw_status),
        'full_diff': {**pin(full_diff), 'coverage': 'all text hunks read; binary ZIP deletion metadata authenticated'},
        'complete_text_diff': {**pin(text_diff), 'lines': len(text_diff.splitlines()), 'human_read': 'complete'},
        'archives': [{**record(ARRIVAL, ZIP), 'parent_identical': True, 'deleted_at_placement': True, 'members': members}],
        'internal_manifest_matches': internal, 'placements': placed, 'host_status': host,
        'prior_review': prior,
        'scope': {'supplied_program_execution': False, 'supplied_program_import': False, 'predecessor_execution': False,
                  'build_or_pdf_read': False, 'full_manuscript_reaudit': False, 'repository_mutation': False,
                  'new_source_read_spans': [[720,780],[939,1093]], 'own_checker_only': True},
        'totals': {'archives': 1, 'members': len(members), 'placed_files': len(placed), 'placed_bytes': sum(x['bytes'] for x in placed),
                   'placed_text_lines': sum(x['read_spans'][0]['lines'] for x in placed),
                   'new_archive_read_lines': sum(s['lines'] for x in members for s in x['read_spans']),
                   'new_manuscript_read_lines': 216, 'host_guide_read_lines': 100},
        'reviewer_helper_sha256': sha(pathlib.Path(__file__).read_bytes()),
        'result': 'PASS provenance; five-file placement only, no Part XVII body publication or new compiler claim established',
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=pathlib.Path, required=True)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    args = parser.parse_args()
    result = run(args.root)
    with args.output.open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print('PASS: 9 members, 5 exact placements, 4 internal hashes, 17 inherited spans; host unchanged')

if __name__ == '__main__':
    main()
