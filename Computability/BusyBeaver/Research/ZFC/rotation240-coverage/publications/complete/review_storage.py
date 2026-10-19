#!/usr/bin/env python3
"""Own read-only packaging reviewer; no supplied helper or proof execution."""
from pathlib import Path, PurePosixPath
import hashlib, json, posixpath, re

HERE = Path(__file__).resolve().parent
OLD = Path('/tmp/zfc-rotation240-coverage-complete-publication/map.json')
NEW = Path('/tmp/zfc-rotation240-coverage-complete-publication-split/map.json')
OLD_SHA = '2ce63c066fa2023e031154f9b9056f7ccbcfabe250b86eb11f57365336f35cdf'
NEW_SHA = '28c2a2bb3dc722b671a8f4958ff1652044344e608a5a543e414129987942ab70'
PREFIX = 'Computability/BusyBeaver/Research/ZFC/rotation240-coverage/publications/complete/'
ARCHIVE_SHA = '35e19e6603b4cd37ebe4148d7ede59ae1c7388cb99d25b772751408215417097'
SIZE = 129525059
LIMIT = 32 * 1024 * 1024
checks = 0
inputs = {}

def need(ok, message):
    global checks
    checks += 1
    if not ok:
        raise AssertionError(message)

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        while data := f.read(1024 * 1024):
            h.update(data)
    return h.hexdigest()

def pin(path, expected=None):
    p = Path(path)
    need(p.is_file() and not p.is_symlink(), 'Regular unchanged input required: ' + str(p))
    digest = sha(p)
    need(expected is None or digest == expected, 'Input digest differs: ' + str(p))
    need(str(p) not in inputs or inputs[str(p)] == digest, 'Conflicting path identity.')
    inputs[str(p)] = digest
    return p

def desc(path):
    p = pin(path)
    return dict(path=str(p), sha256=inputs[str(p)])

def main():
    need(__debug__, 'Optimized reader forbidden.')
    a = json.loads(pin(OLD, OLD_SHA).read_text())
    b = json.loads(pin(NEW, NEW_SHA).read_text())
    old = {q['target']: q for q in a['files']}
    new = {q['target']: q for q in b['files']}
    need(len(a['files']) == len(old) == 872 and len(b['files']) == len(new) == 877, 'Exact map census.')
    removed = PREFIX + 'history.json.gz'
    added = {PREFIX + n for n in ['README.md', 'history-parts.json', *[f'history.json.gz.part-{i:02}' for i in range(4)]]}
    need(old.keys() - new.keys() == {removed} and new.keys() - old.keys() == added, 'Only the exact archive split may change the target set.')
    need(len(old.keys() & new.keys()) == 871, 'Unchanged-target census.')
    for target in old.keys() & new.keys():
        need(old[target] == new[target], 'An existing target descriptor changed: ' + target)
    for key in a:
        if key not in {'status', 'files'}:
            need(a[key] == b[key], 'Other map metadata changed: ' + key)
    need(a['status'] == 'REVIEWABLE_METADATA_PACKET_NOT_INSTALLED' and b['status'] == 'REVIEWABLE_LOSSLESS_SPLIT_PACKET_NOT_INSTALLED', 'Publication state scope.')
    need(not a['proof_execution'] and not b['proof_execution'], 'Packaging must not claim proof execution.')
    for target, q in new.items():
        p = PurePosixPath(target)
        need(not p.is_absolute() and '..' not in p.parts and str(p) == target, 'Unsafe/noncanonical target.')
        source = pin(q['source'], q['sha256'])
        need(source.stat().st_size == q['bytes'], 'Mapped byte size differs.')
    original = pin(old[removed]['source'], ARCHIVE_SHA)
    need(old[removed]['sha256'] == ARCHIVE_SHA and old[removed]['bytes'] == original.stat().st_size == SIZE, 'Original archive identity.')
    index = json.loads(Path(new[PREFIX + 'history-parts.json']['source']).read_text())
    names = [f'history.json.gz.part-{i:02}' for i in range(4)]
    need(index['format'] == 'ordered byte chunks of one unchanged gzip stream' and index['proof_or_history_content_changes'] is False, 'Index split scope.')
    need(index['original_archive'] == dict(file='history.json.gz', bytes=SIZE, sha256=ARCHIVE_SHA), 'Index original archive.')
    need(index['original_publication_map'] == dict(path=str(OLD), sha256=OLD_SHA), 'Index original map.')
    need([q['file'] for q in index['parts']] == names, 'Exact four-part order.')
    h = hashlib.sha256(); total = 0
    with original.open('rb') as before:
        for i, q in enumerate(index['parts']):
            part = new[PREFIX + q['file']]
            need(q == dict(file=names[i], bytes=part['bytes'], sha256=part['sha256']), 'Index/map part identity.')
            need(0 < q['bytes'] <= LIMIT and (i == 3 or q['bytes'] == LIMIT), 'Part exceeds bound or has unexpected boundary.')
            with Path(part['source']).open('rb') as stream:
                while data := stream.read(1024 * 1024):
                    need(before.read(len(data)) == data, 'Concatenation differs from original bytes.')
                    h.update(data); total += len(data)
        need(before.read(1) == b'', 'Original archive has unmatched suffix.')
    need(total == SIZE and h.hexdigest() == ARCHIVE_SHA, 'Complete concatenation identity.')
    storage = b['history_storage']
    need(storage == dict(format=index['format'], original_archive_sha256=ARCHIVE_SHA, parts=4, index_target=PREFIX + 'history-parts.json', original_map=dict(path=str(OLD), sha256=OLD_SHA)), 'Map storage descriptor.')
    readme = Path(new[PREFIX + 'README.md']['source']).read_text()
    need('cat ' + ' '.join(names) + ' > /tmp/rotation240-coverage-history.json.gz' in readme, 'README must reconstruct ordered original stream.')
    need('sha256sum /tmp/rotation240-coverage-history.json.gz' in readme and ARCHIVE_SHA in readme and '129,525,059 bytes' in readme and '32 MiB' in readme, 'README identity and size instructions.')
    links = re.findall(r'\[[^\]]+\]\(([^)]+)\)', readme)
    need(links == ['../../../rotation240_coverage_complete.md', 'history-parts.json'], 'Unexpected README links.')
    for link in links:
        target = posixpath.normpath(PREFIX + link)
        need(target in new and Path(new[target]['source']).is_file(), 'README relative link does not resolve within map.')
    pin(__file__)
    for path, digest in inputs.items():
        need(sha(path) == digest, 'Input changed before close: ' + path)
    result = dict(status='LOSSLESS_SPLIT_PUBLICATION_REVIEW_PASS', findings=[], reviewer_role='Independent packaging check; author of the separate complete-coverage evidence reviewer. This check executes no publisher, proof, compiler or delivered helper.', original_map=dict(path=str(OLD), sha256=OLD_SHA), successor_map=dict(path=str(NEW), sha256=NEW_SHA), unchanged_targets=871, removed_archive_target=removed, added_targets=sorted(added), selected_targets=877, original_archive=dict(bytes=SIZE, sha256=ARCHIVE_SHA), part_bytes=[q['bytes'] for q in index['parts']], maximum_part_bytes=LIMIT, concatenation_byte_equality=True, index_and_readme_checked=True, relative_coverage_link='Computability/BusyBeaver/Research/ZFC/rotation240_coverage_complete.md', scope='External reviewable split packet only. The exact original gzip stream and all other target bytes are preserved; no new proof or installed-state claim.', checks=checks, inputs=[dict(path=p, sha256=h) for p, h in sorted(inputs.items())], reviewer_source=desc(__file__), supplied_program_execution=False, compiler_execution=False, maintained_writes=False)
    target = HERE / 'review.json'
    need(not target.exists(), 'Fresh review output required.')
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], receipt=desc(target), checks=result['checks'], files=len(inputs)), indent=2))

if __name__ == '__main__':
    main()
