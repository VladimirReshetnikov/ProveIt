"""Fresh read-only byte-placement checker. Never imports supplied code."""
import hashlib
import io
import json
import re
import subprocess
import zipfile
from pathlib import Path

REPO = Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT = '12076b2e8b4806efe46b1588926eeed2809c0952'
PRIOR = Path('/tmp/review_polish_partx_c9bc70d8f.json')
PRIOR_SHA = '3eb296146ce0233db75deb835e7568ace428f247399e6252a1131bd570e290f8'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def need(x, msg):
    if not x:
        raise ValueError(msg)

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

def at(c, p):
    return git('show', c + ':' + p)

def info(c, p):
    b = at(c, p)
    return {'path': p, 'commit': c, 'blob': git('rev-parse', c + ':' + p).decode().strip(),
            'bytes': len(b), 'sha256': sha(b)}

def labels(b):
    return re.findall(rb'\\label(?:\[[^\]]*\])?\{([^}]*)\}', b)

def main():
    raw = PRIOR.read_bytes()
    need(sha(raw) == PRIOR_SHA, 'prior receipt pin')
    prior = json.loads(raw)
    arrival = prior['new_arrivals']['commit']
    parent = git('rev-parse', COMMIT + '^').decode().strip()
    by_hash = {}
    archives = []
    for a in prior['new_arrivals']['archives']:
        b = at(arrival, a['path'])
        need(sha(b) == a['sha256'], 'archive pin ' + a['path'])
        z = zipfile.ZipFile(io.BytesIO(b))
        members = {x.filename: z.read(x) for x in z.infolist() if not x.is_dir()}
        need(len(members) == len(a['members']), 'member census')
        for m in a['members']:
            v = members[m['path']]
            need(sha(v) == m['sha256'] and len(v) == m['bytes'], 'member pin')
            by_hash.setdefault(sha(v), []).append((a['path'], m, v))
        archives.append(a)
    changes = [s.split('\t') for s in git('diff-tree', '--no-commit-id', '--name-status', '-r', COMMIT).decode().splitlines()]
    additions = []
    for status, p in changes:
        if status != 'A':
            continue
        b = at(COMMIT, p)
        matches = by_hash.get(sha(b), [])
        need(matches and all(v == b for _, _, v in matches), 'unmatched addition ' + p)
        rec = info(COMMIT, p)
        rec['byte_identical_archive_members'] = [
            {'archive': a, 'member': m['path'], 'prior_coverage': m['coverage']} for a, m, _ in matches]
        rec['coverage'] = 'whole-file byte equality; prior human coverage transfers only where explicitly recorded'
        additions.append(rec)
    roots = [
        'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets',
        'Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic',
        'Algebra/SurrealNumbers/docs/surreal/discrete-initial-subgroups-and-omnific-normalization',
        'SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games',
    ]
    unchanged = []
    for root in roots:
        for f in ['article.tex', 'README.md']:
            p = root + '/' + f
            old, new = at(parent, p), at(COMMIT, p)
            need(old == new, 'unexpected host write ' + p)
            rec = info(COMMIT, p)
            rec.update({'parent_blob': git('rev-parse', parent + ':' + p).decode().strip(),
                        'unchanged': True, 'coverage': 'whole-file equality only; no new full prose read'})
            if f.endswith('.tex'):
                ls = labels(new)
                rec['label_count'] = len(ls)
                rec['expected_new_prefixes_present'] = {prefix: any(x.startswith(prefix.encode()) for x in ls)
                    for prefix in ['hset:ns:', 'pma:lgc:', 'pma:gcm:', 'isg:ptg:', 'mbg:hat:']}
            unchanged.append(rec)
    deleted = [p for status, p in changes if status == 'D']
    need(sorted(deleted) == sorted(a['path'] for a in archives), 'retired archives')
    need([p for status, p in changes if status == 'M'] == ['SetTheory/Cardinals/.gitattributes'], 'modified file census')
    need(len(additions) == 32 and sum(x['bytes'] for x in additions) == 371628, 'addition census')
    attr = info(COMMIT, 'SetTheory/Cardinals/.gitattributes')
    text = at(COMMIT, attr['path']).decode().splitlines()
    span = '\n'.join(text[231:234]) + '\n'
    need('02-hat-surplus-example_prefix.csv -text' in span, 'CRLF attribute')
    attr['human_read_spans'] = [{'first': 232, 'last': 234, 'normalized_utf8_sha256': sha(span.encode())}]
    return {'schema': 'batch90-placement-review-v1', 'commit': COMMIT, 'parent': parent,
            'prior_review_json_sha256': PRIOR_SHA, 'checker_sha256': sha(Path(__file__).read_bytes()),
            'archives': archives, 'additions': additions, 'unchanged_host_files': unchanged,
            'attribute_delta': attr, 'retired_archive_paths': deleted,
            'executed_supplied_programs': False, 'executed_supplied_builds': False,
            'read_scope': 'All 53 prior archive-member bytes and all 32 placed-file bytes compared; existing eight host article/README bytes compared; source-label census only; no new manuscript proof audit.',
            'counts': {'archives': len(archives), 'archive_members': sum(len(a['members']) for a in archives),
                       'added_files': len(additions), 'added_bytes': sum(x['bytes'] for x in additions),
                       'unchanged_host_files': len(unchanged)}}

if __name__ == '__main__':
    print(json.dumps(main(), indent=2, sort_keys=True))
