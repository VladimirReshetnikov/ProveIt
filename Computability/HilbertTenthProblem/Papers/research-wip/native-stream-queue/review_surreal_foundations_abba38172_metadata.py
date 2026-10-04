#!/usr/bin/env python3
"""Fresh read-only Git/ZIP metadata audit. Does not load any predecessor program."""
from pathlib import Path, PurePosixPath
import argparse
import collections
import hashlib
import io
import json
import re
import subprocess
import zipfile

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT = 'abba381729f85fd28f997ab2a7eefa1b8d1bf242'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/'
ARRIVAL = 'ec91f8c7c5dbe1e34aef03214e441a1c0154f410'
PLACEMENT = '350b9a954d302554e04d510f5ee9f220042ed75c'
STEM = Path('/tmp/review_surreal_foundations_abba38172')
LABEL = re.compile(r'\\label\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}')
REF = re.compile(r'\\(?:[Cc](?:page)?ref|(?:eq|page|auto)?ref)\*?(?:\[[^\]]*\])?\{([^}]+)\}')

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def blob(commit, path):
    return git('show', commit + ':' + path)

def digest(data):
    return {'bytes': len(data), 'sha256': sha(data)}

def spans(data, ranges):
    lines = data.splitlines(keepends=True)
    records = []
    for start, end, purpose in ranges:
        require(1 <= start <= end <= len(lines), 'Invalid span')
        part = b''.join(lines[start - 1:end])
        records.append({'start_line': start, 'end_line': end,
                        'purpose': purpose, **digest(part)})
    return records

def file_record(commit, path, coverage='byte authentication only', ranges=()):
    data = blob(commit, path)
    result = {'commit': commit, 'path': path,
              'blob_oid': git('rev-parse', commit + ':' + path).decode().strip(),
              **digest(data), 'coverage': coverage}
    if not path.endswith(('.pdf', '.zip')):
        result['lines'] = len(data.splitlines())
        result['read_spans'] = spans(data, ranges)
    return result

def label_records(data):
    text = data.decode('utf-8')
    return [{'label': m.group(1), 'line': text.count('\n', 0, m.start()) + 1}
            for m in LABEL.finditer(text)]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--expect', type=Path)
    args = ap.parse_args()
    parent = git('rev-parse', COMMIT + '^').decode().strip()
    paths = git('diff-tree', '--no-commit-id', '--name-only', '-r', COMMIT).decode().splitlines()
    require(set(paths) == {HOST + x for x in ('README.md', 'article.tex', 'article.pdf')}, 'changed paths')
    result = {'schema': 'bounded-publication-review-v1', 'commit': COMMIT, 'parent': parent,
              'helper_sha256': sha(Path(__file__).read_bytes()),
              'execution': 'Only this new standard-library metadata collector; Git reads and ZIP reads. No supplied/frozen code, builds, imports or external fetches.',
              'changed_files': [], 'diffs': [], 'context': [], 'archives': [], 'placements': []}
    article_ranges = [(7633, 8575, 'Part IX introduction, notation, correspondence/status claims, logical conventions, imported sign facts and bit storage'),
                      (8729, 9417, 'Graph validity/equality/membership/collapse and Choice, full round trip, effective axiom recipe'),
                      (9467, 11844, 'Provability and persistence; canonical reduct criterion; quotient birthday; automorphisms; reflection/class boundaries; class correspondence/variants; computational/status/provenance sections')]
    guide = blob(COMMIT, HOST + 'README.md')
    guide_ranges = [(1, 75, 'Guide header, file inventory and label-count claims'),
                    (229, 269, 'Source merge and new-result summaries')]
    for path in paths:
        result['changed_files'].append({'before': file_record(parent, path),
                                       'after': file_record(COMMIT, path,
                                           'Selected text spans plus full guide diff' if path.endswith('README.md') else
                                           'Selected Part IX text; not full manuscript certification' if path.endswith('.tex') else 'PDF bytes only; not rendered or page-count checked',
                                           guide_ranges if path.endswith('README.md') else article_ranges if path.endswith('.tex') else ())})
        data = git('diff', '--no-ext-diff', '--no-color', '--unified=3', parent, COMMIT, '--', path)
        result['diffs'].append({'path': path, **digest(data), 'lines': len(data.splitlines()),
                                'coverage': 'full textual diff read' if path.endswith('README.md') else 'diff hash/statistics only; exact selected source spans recorded separately'})
    agents_path = 'Algebra/SurrealNumbers/AGENTS.md'
    agents = blob(COMMIT, agents_path)
    result['context'].append(file_record(COMMIT, agents_path, 'full instructions read', [(1, len(agents.splitlines()), 'Applicable agent instructions')]))
    result['context'].append(file_record(COMMIT, 'docs/incoming/README.md', 'standing retention rule read', [(425, 439, 'Never drop unproved or wrong claims')]))
    prior_path = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_new_foundations_f300069cf.md'
    prior = blob(COMMIT, prior_path)
    require(prior == (ROOT / prior_path).read_bytes(), 'Context read agrees with immutable bytes')
    result['context'].append(file_record(COMMIT, prior_path, 'full prior bounded intake read inertly, not re-executed', [(1, len(prior.splitlines()), 'Prior coverage boundary and intake pins')]))
    prior_json_path = prior_path[:-3] + '.json'
    result['context'].append(file_record(COMMIT, prior_json_path, 'byte authentication and first two archive hashes checked only'))
    require(sha(blob(COMMIT, prior_json_path)) == '49264495f8221a89191076344d2d9ccb89412ad5883e3b9791e7cbae3c8fff81', 'prior receipt binding')
    new_article = blob(COMMIT, HOST + 'article.tex')
    old_article = blob(parent, HOST + 'article.tex')
    old_labels, new_labels = label_records(old_article), label_records(new_article)
    old_names, new_names = {x['label'] for x in old_labels}, {x['label'] for x in new_labels}
    require(len(new_names) == len(new_labels), 'No duplicate host labels')
    require(old_names <= new_names, 'No removed parent labels')
    added = sorted(new_names - old_names)
    require(len(old_labels) == 372 and len(new_labels) == 523 and len(added) == 151, 'host label counts')
    require(all(x.startswith('hset:sf:') for x in added), 'new-label prefix')
    refs = []
    text = new_article.decode()
    # Literal local TeX references; not printed external \lbl names or macro expansion.
    for m in REF.finditer(text):
        for name in m.group(1).split(','):
            name = name.strip()
            refs.append({'label': name, 'line': text.count('\n', 0, m.start()) + 1})
    missing_refs = sorted({r['label'] for r in refs if r['label'] not in new_names and '#' not in r['label']})
    require(not missing_refs, 'Literal unresolved local references: ' + repr(missing_refs))
    result['host_labels'] = {'before': old_labels, 'after': new_labels, 'added': added, 'removed': [],
                             'literal_references': refs, 'missing_literal_references': missing_refs,
                             'scope': 'Literal label/reference syntax only; no TeX expansion, statement-number certification or PDF checking'}
    route_specials = {
       13: {'sec:scope':['sec:intro'], 'thm:noGBCinZFC':['thm:noint'], 'prop:diagonal':['thm:diagonal'],
            'sec:repo':['sub:machine','sub:repo'], 'sec:conclusion':['sec:provenance'],
            'app:formulas':['sub:formulas','sub:ledger']},
       14: {'sec:answer':['sec:intro'], 'sec:sources':['sec:intro','sub:repo'], 'sec:codes':['sec:graphs'],
            'sec:omnific':['sub:qb'], 'lem:fractions':['prop:fractions'], 'prop:pure':['prop:rcf'],
            'sec:reflection':['sub:reflection'], 'sec:alternatives':['sec:bounds','sub:inaccessible'],
            'sec:conclusion':['sec:provenance'], 'app:formula':['sub:formulas'], 'app:ledger':['sub:ledger']}}
    archival = [
        (13, 'surreal_omnific_foundations.zip', 'db8e989962143836b5c6c9520167d258c1d922cb69295bc14b65e9824ca1013c',
         'surreal_omnific_foundations/', 'surreal_omnific_foundations.tex', ['README.txt']),
        (14, 'Surreal_Only_Foundations_and_NBG.zip', '22ef255d65a2dfa9b92f717cadb0f2412cd1455853da30cee9ce991f317f11c7',
         'Surreal_Only_Foundations/', 'article.tex', ['README.md','SOURCES_AND_STATUS.md'])]
    source_routes = []
    for number, name, expected_sha, prefix, texname, fully_read in archival:
        path = 'docs/incoming/' + name
        data = blob(ARRIVAL, path)
        require(sha(data) == expected_sha, 'archive pin')
        zf = zipfile.ZipFile(io.BytesIO(data))
        members = [x for x in zf.infolist() if not x.is_dir()]
        require(len({x.filename for x in members}) == len(members), 'No duplicate members')
        record = {**file_record(ARRIVAL, path), 'source_number': number, 'members': []}
        for info in members:
            content = zf.read(info)
            relative = info.filename.removeprefix(prefix)
            rec = {'path': info.filename, **digest(content), 'coverage': 'bytes only; not executed/imported'}
            if relative in fully_read:
                rec['coverage'] = 'full guide/status text read'
                rec['read_spans'] = spans(content, [(1, len(content.splitlines()), 'Delivered scope/status guide')])
            if relative == texname:
                labels = label_records(content)
                rec.update({'lines':len(content.splitlines()), 'labels':labels,
                            'raw_backslash_label_count':content.count(b'\\label'),
                            'question_environments':len(re.findall(rb'\\begin\{question\}',content)),
                            'bibliography_entries':len(re.findall(rb'\\bibitem',content)),
                            'coverage':'Label/provenance metadata only; delivered manuscript body not re-audited'})
                require(len(labels) == (59 if number == 13 else 54), 'source label count')
                for lab in labels:
                    old = lab['label']
                    targets = ['hset:sf:' + x for x in route_specials[number].get(old, [old])]
                    require(all(x in new_names for x in targets), 'mapped label exists')
                    source_routes.append({'source_number': number, 'source_label': old, 'source_line': lab['line'],
                                          'target_labels': targets, 'mode': 'manual subject route' if old in route_specials[number] else 'prefix route',
                                          'scope': 'Destination locator exists; not assertion of verbatim text or independently verified full proof equivalence'})
            record['members'].append(rec)
        if number == 14:
            ledger = zf.read(prefix + 'SHA256SUMS').decode()
            checks = []
            for line in ledger.splitlines():
                h, relative = line.split(None, 1)
                relative = relative.lstrip('* ')
                content = zf.read(prefix + relative)
                require(sha(content) == h, 'archive checksum ledger')
                checks.append({'member': prefix + relative, 'sha256': h})
            require(len(checks) == 8, 'eight ledger entries')
            record['supplied_checksum_entries_independently_matched'] = checks
            mapping = {'SOURCES_AND_STATUS.md':'14-surreal-only-nbg-SOURCES_AND_STATUS.md',
                       'verify_finite.py':'code/14-surreal-only-nbg-verify_finite.py',
                       'build.sh':'code/14-surreal-only-nbg-build.sh',
                       'verification.json':'data/14-surreal-only-nbg-verification.json',
                       'build_validation.json':'data/14-surreal-only-nbg-build_validation.json'}
            for source, destination in mapping.items():
                original = zf.read(prefix + source)
                first = blob(PLACEMENT, HOST + destination)
                placed = blob(COMMIT, HOST + destination)
                require(original == first == placed, 'placed member identity')
                result['placements'].append({'source_number':number, 'archive_member':prefix + source,
                                             'first_placement':file_record(PLACEMENT, HOST + destination),
                                             'at_publication':file_record(COMMIT, HOST + destination),
                                             'exact_archive_byte_match':True})
        result['archives'].append(record)
    result['source_label_routes'] = source_routes
    require(len(source_routes) == 113, 'all original literal label locators')
    ancestors = []
    for short in ['722337445','bd1de458b','fb2287290',ARRIVAL,PLACEMENT]:
        full = git('rev-parse', short).decode().strip()
        test = subprocess.run(['git','merge-base','--is-ancestor',full,COMMIT],cwd=ROOT,check=False)
        require(test.returncode == 0, 'declared provenance ancestor')
        ancestors.append(full)
    result['declared_ancestors_verified'] = ancestors
    result['findings'] = [
       {'id':'R1','kind':'missing effective-axiomatization premise', 'article_lines':[9522,9541],
        'label':'hset:sf:lem:persist', 'original':'if $\\Sigma$ is recursive, so is the second theory.',
        'counterexample':'S=T=Th(N), identity interpretations, Sigma empty; T is not computably axiomatizable.',
        'correction':'Assume T has a computably enumerable axiom set, Sigma is computably enumerable, and the interpretation translation is computable; then the extension is computably axiomatizable. Dovetail both axiom enumerations.',
        'impact':'Generic lemma only; the actual finite-language ZFC/class applications already have effective source axiomatizations and computable fixed-formula translations.'},
       {'id':'R2','kind':'incorrect delivered-label inventory','readme_lines':[[61,61],[225,227]],
        'article_lines':[11777,11781], 'original_counts':[76,70], 'verified_counts':[59,54],
        'impact':'Provenance metadata only; merged372+151=523 and all old labels preserved.'}]
    result['scope_limits'] = [
       'No full article-diff read: full guide diff and recorded Part IX source spans only.',
       'No complete source-body merge equivalence check; source routes are locators and labels only.',
       'No external source fetch, imported omnific-sign/Hahn/class-forcing proof audit, Lean build, finite-suite run or PDF inspection.',
       'No claim of a finite ordinary-integer evaluator, existential integer witness compilation or paid arithmetic improvement.',
       'Immutable publication checkpoint only; any subsequent root corrections are outside this receipt.']
    result['totals'] = {'changed_paths':len(paths), 'before_after_blobs':2*len(paths),
                        'archives':len(result['archives']), 'archive_members':sum(len(x['members']) for x in result['archives']),
                        'placed_files':len(result['placements']), 'checksum_entries':8,
                        'host_labels_before':len(old_labels), 'host_labels_after':len(new_labels),
                        'new_sf_labels':len(added), 'source_labels':len(source_routes),
                        'literal_reference_occurrences':len(refs),
                        'selected_article_lines':sum(b-a+1 for a,b,_ in article_ranges),
                        'full_guide_diff_lines':result['diffs'][[x['path'] for x in result['diffs']].index(HOST+'README.md')]['lines']}
    encoded = (json.dumps(result, indent=2, ensure_ascii=False) + '\n').encode()
    if args.expect:
        require(encoded == args.expect.read_bytes(), 'Receipt differs from expected')
    else:
        STEM.with_suffix('.json').write_bytes(encoded)
    print(json.dumps({'status':'PASS', 'receipt_sha256':sha(encoded), **result['totals']},sort_keys=True))

if __name__ == '__main__':
    main()
