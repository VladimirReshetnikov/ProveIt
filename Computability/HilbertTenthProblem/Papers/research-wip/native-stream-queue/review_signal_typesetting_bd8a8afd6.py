#!/usr/bin/env python3
"""Source-only, occurrence-preserving transfer audit for bd8a8afd6.

Reads pinned Git blobs and ZIP bytes. No author modules, suites, repository
writes or PDF builds. All repeated source occurrences consume distinct,
ordered occurrences in the corresponding Part and appendices.
"""
import argparse
from collections import Counter
import difflib
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import zipfile

COMMIT = 'bd8a8afd67108107c1fe443e488b84ef05236d78'
PARENT = 'ae7c1e6aae3dc58c9c638b35646865ad6c10387d'
ARCHIVE_REF = '38edfb31e40af6aa99c9d552a47e111d3f3eb8da'
REPORT = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS = {
 'article.tex': '74a15d44a7cd23d1ffe813bb6d70bd61986bc93a43615504176c2f756505f239',
 'README.md': 'ebe0ba2754003afb46f8771399e420c5594edb5f9b1bb605a44b4719ec250201',
 'article.pdf': 'fe5e275afec2f381801a403538bae36efd8cfcd119cee69478e2733b14b55b8a',
}
BASIS = {
 'placement_a7ae02511_inventory.json': 'cec197a4c1367d9dcd671ba85fa242fbdaba5445251794535f0333c2228687cf',
 'review_conservative_signal_corrected_aebfa386e.md': '7d108ff2eeb529d9a012da78bf55d5059b250c170a01376833079d354082d677',
 'review_signal_guard_projection_independent.md': 'a00caeefa48f527ad4b46a15ef55e2c5b951264c7d3b8e28f39588e85b31f277',
 'review_sparse_lattice_aebfa386e.md': '5e8c1e4cf5c8617c2a1f047e4a8b40dad1f6c05c3b339daaa91ddcedc1391ee0',
 'sparse_lattice_projection.md': '89f9f1b288f3a919a61f3c27469aca82b5e05c56bab1b3896eef67095d503551',
 'review_sparse_projection_aebfa.md': '6ec8bb868e0a94f4206533ddd59279403650414df0d26a04f250af91c197a0d9',
}
ARCHIVES = {
 'signal': ('docs/incoming/Conservative_Signal_Frontend_Corrected.zip', 'e2acf725fcf017e14b2705cc9097fa9e3eb8b02c2fc9faf8ce486d3614816990', 45),
 'sparse': ('docs/incoming/Sparse_Lattice_Diophantine_Certificates.zip', '90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68', 49),
}
OLD = 'whose event dynamics is an 18-dimensional integer-linear map with a canonical quadratic step certificate'
NEW = 'whose event dynamics is an 18-dimensional partial piecewise homogeneous integer-linear map with a canonical quadratic step certificate'
PATCH_NAME = 'signal_typesetting_bd8a8afd6_partial_map.patch'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], check=True, capture_output=True, timeout=90).stdout


def normalize(text):
    text = re.sub(r'(?<!\\)%[^\n]*', '', text)
    text = text.replace('smc:cs:', '').replace('smc:sl:', '')
    text = re.sub(r'\\label(?:\[[^]]*\])?\{[^}]*\}', '', text)
    text = re.sub(r'\\N\b', r'\\NN', text)
    text = text.replace('dl2007', 'DL07').replace('dl2006', 'DL06')
    return re.sub(r'\s+', '', text)


def blocks(text, kind):
    if kind == 'formal':
        rx = r'\\begin\{(theorem|lemma|proposition|corollary|definition|remark|proof)\}(.*?)\\end\{\1\}'
        return [dict(start=m.start(), environment=m.group(1), body=m.group(0)) for m in re.finditer(rx, text, re.S)]
    if kind == 'display':
        rx = r'\\\[(.*?)\\\]|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.*?)\\end\{\2\}'
        return [dict(start=m.start(), environment=m.group(2) or 'display', body=m.group(0)) for m in re.finditer(rx, text, re.S)]
    need(kind == 'inline', 'unknown block category')
    return [dict(start=m.start(), environment='inline', body=m.group(0)) for m in re.finditer(r'(?<!\\)\$(.*?)(?<!\\)\$', text, re.S)]


def ordered_match(needles, haystack):
    cursor, matched = 0, []
    for needle in needles:
        found = next((j for j in range(cursor, len(haystack)) if needle == haystack[j]), None)
        need(found is not None, 'missing distinct ordered occurrence')
        matched.append(found)
        cursor = found+1
    need(len(set(matched)) == len(matched), 'occurrence reused')
    return matched


def verify(repo, patch):
    repo = Path(repo).resolve()
    need(git(repo, 'rev-parse', COMMIT+'^').decode().strip() == PARENT, 'parent commit differs')
    source = {n: git(repo, 'show', COMMIT+':'+REPORT+'/'+n) for n in PINS}
    need({n: sha(b) for n, b in source.items()} == PINS, 'typeset source pin differs')
    basis = {n: git(repo, 'show', COMMIT+':'+WIP+'/'+n) for n in BASIS}
    need({n: sha(b) for n, b in basis.items()} == BASIS, 'review-basis pin differs')
    inventory = json.loads(basis['placement_a7ae02511_inventory.json'])
    archive_records, members = {}, {}
    placements = []
    for package, (name, pin, size) in ARCHIVES.items():
        data = git(repo, 'show', ARCHIVE_REF+':'+name)
        need(sha(data) == pin, 'archive pin differs')
        z = zipfile.ZipFile(io.BytesIO(data))
        payload = {}
        for info in z.infolist():
            path = PurePosixPath(info.filename)
            need(not path.is_absolute() and '..' not in path.parts and '\\' not in info.filename and not stat.S_ISLNK(info.external_attr >> 16), 'unsafe ZIP member')
            if info.is_dir():
                continue
            need(info.filename not in payload, 'duplicate ZIP member')
            payload[info.filename] = z.read(info)
        need(len(payload) == size, 'archive member count differs')
        manifest = next(a for a in inventory['archives'] if a['path'] == name)
        member_hashes = {n: sha(b) for n, b in payload.items()}
        need(member_hashes == {m['member']: m['sha256'] for m in manifest['members']}, 'full member manifest differs')
        for member in manifest['members']:
            for target in member['placed_paths']:
                need(target.startswith(REPORT+'/'), 'wrong source-aware report target')
                need(git(repo, 'show', COMMIT+':'+target) == payload[member['member']], 'placed companion changed')
                placements.append(dict(package=package, member=member['member'], target=target, sha256=member['sha256']))
        members[package] = payload
        archive_records[package] = dict(path=name, git_ref=ARCHIVE_REF, sha256=pin, members=len(payload), member_sha256=member_hashes)
    text = source['article.tex'].decode()
    old_signal = members['signal']['conservative-signal-release/paper/conservative-signal-diophantine.tex'].decode()
    old_signal = old_signal.replace('\\input{morita-table.tex}', members['signal']['conservative-signal-release/paper/morita-table.tex'].decode())
    old_sparse = members['sparse']['sparse-lattice-release/paper/sparse-lattice.tex'].decode()
    for name in ('core', 'source', 'barriers', 'semilinearity', 'reproduction'):
        old_sparse = old_sparse.replace('\\input{'+name+'.tex}', members['sparse']['sparse-lattice-release/paper/'+name+'.tex'].decode())
    need('\\input{' not in old_signal and '\\input{' not in old_sparse, 'unexpanded source input')
    a = text.index('\\part{Conservative signal machines')
    b = text.index('\\part{Sparse Diophantine')
    c = text.index('\\appendix')
    d = text.index('\\section{Part~III: the complete Morita')
    e = text.index('\\begin{thebibliography}')
    ranges = {'signal': [(a, b), (d, e)], 'sparse': [(b, c)]}
    records = {}
    for package, old in (('signal', old_signal), ('sparse', old_sparse)):
        kinds = {}
        for kind in ('formal', 'display', 'inline'):
            src = blocks(old, kind)
            dst = []
            for left, right in ranges[package]:
                dst.extend(dict(v, start=v['start']+left) for v in blocks(text[left:right], kind))
            match = ordered_match([normalize(v['body']) for v in src], [normalize(v['body']) for v in dst])
            kinds[kind] = dict(source_count=len(src), matched_distinct_occurrences=len(match), source_environment_counts=dict(Counter(v['environment'] for v in src)),
                occurrence_map=[dict(source_occurrence=i, target_occurrence=j, target_line=text.count('\n', 0, dst[j]['start'])+1, normalized_sha256=sha(normalize(src[i]['body']).encode())) for i, j in enumerate(match)])
        labels = re.findall(r'\\label(?:\[[^]]*\])?\{([^}]+)\}', old)
        prefix = 'smc:cs:' if package == 'signal' else 'smc:sl:'
        target_labels = re.findall(r'\\label(?:\[[^]]*\])?\{([^}]+)\}', text)
        need(len(set(labels)) == len(labels), 'source duplicate label')
        need(all(target_labels.count(prefix+label) == 1 for label in labels), 'label missing or duplicated')
        records[package] = dict(blocks=kinds, source_labels=len(labels), preserved_source_labels=[prefix+v for v in labels])
    need([(records[p]['blocks'][k]['source_count']) for p in ('signal', 'sparse') for k in ('formal', 'display', 'inline')] == [11, 46, 452, 12, 60, 497], 'coverage census differs')
    regressions = 0
    for needles, haystack in ((['x', 'x'], ['x']), (['a', 'b'], ['b', 'a']), (['x'], [])):
        try:
            ordered_match(needles, haystack)
        except ValueError:
            regressions += 1
        else:
            raise ValueError('multiplicity/order regression accepted')
    need(ordered_match(['x', 'x'], ['x', 'y', 'x']) == [0, 2], 'repeated occurrence positive control')
    changed = git(repo, 'diff-tree', '--no-commit-id', '--name-status', '-r', COMMIT).decode().splitlines()
    need(changed == [f'M\t{REPORT}/README.md', f'M\t{REPORT}/article.pdf', f'M\t{REPORT}/article.tex'], 'unexpected changed source')
    # This one wording repair affects the new overview only, not the theorem.
    need(text.count(OLD) == 1, 'abstract repair context changed')
    repaired = text.replace(OLD, NEW)
    expected_patch = ''.join(difflib.unified_diff(text.splitlines(True), repaired.splitlines(True), fromfile='a/'+REPORT+'/article.tex', tofile='b/'+REPORT+'/article.tex')).encode()
    need(Path(patch).read_bytes() == expected_patch, 'patch bytes differ')
    with tempfile.TemporaryDirectory(prefix='signal-typesetting-patch-') as temp:
        target = Path(temp)/REPORT
        target.mkdir(parents=True)
        for name, data in source.items():
            (target/name).write_bytes(data)
        subprocess.run(['patch', '--batch', '--forward', '-p1', '-i', str(Path(patch).resolve())], cwd=temp, check=True, capture_output=True, timeout=60)
        need((target/'article.tex').read_text() == repaired, 'private patch output differs')
        need((target/'README.md').read_bytes() == source['README.md'] and (target/'article.pdf').read_bytes() == source['article.pdf'], 'unrelated file changed')
    need(18*80501 == 4196998-2747980 == 2762961-1313943, 'guard projection ledger')
    need(25392522-17903098 == 7489424, 'guard schedule saving')
    return dict(status='PASS_BOUNDED_TRANSFER_WITH_ABSTRACT_QUALIFIER_REPAIR', review_helper_sha256=sha(Path(__file__).read_bytes()), commit=COMMIT, parent=PARENT, typeset_sha256=PINS, review_basis_sha256=BASIS,
        archives=archive_records, companion_member_placements=placements, distinct_companion_files=len({v['target'] for v in placements}), companion_member_identities=len(placements),
        normalization=['strip comments and whitespace','remove label macros','strip smc:cs: and smc:sl: source prefixes','rename natural macro N to NN','rename source citation keys dl2007/dl2006 to DL07/DL06'],
        matching='Consumes distinct occurrences in order within Part III plus its F-H appendices, or Part IV; never set/dictionary membership or cross-Part reuse.', transfer=records,
        matcher_regressions=dict(rejections=regressions, repeated_positive_control=True), changed_files=changed,
        arithmetic=dict(deleted_rows_and_slacks=1449018, old_witnesses=4196998, new_witnesses=2747980, old_squared_rows=2762961, new_squared_rows=1313943, complementarity_products=80501, operation_saving=7489424),
        patch=dict(filename=PATCH_NAME, sha256=sha(expected_patch), before_sha256=PINS['article.tex'], after_sha256=sha(repaired.encode()), private_application='PASS', pdf_rebuild_required=True),
        scope='Pinned semantic typesetting transfer and new editorial relations only. No old Parts I-II proof review, unchanged author suites, module execution, PDF build/layout audit, universal operation improvement or future-commit review.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, default=Path.cwd())
    p.add_argument('--patch', type=Path, default=Path(__file__).with_name(PATCH_NAME))
    p.add_argument('--expect', type=Path)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    result = verify(a.repo, a.patch)
    if a.expect:
        need(exact(result, json.loads(a.expect.read_text())), 'saved receipt differs')
    if a.output:
        a.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(status=result['status'], companions=result['distinct_companion_files'], source_occurrences={k: {t: v['source_count'] for t, v in x['blocks'].items()} for k, x in result['transfer'].items()}), sort_keys=True))
