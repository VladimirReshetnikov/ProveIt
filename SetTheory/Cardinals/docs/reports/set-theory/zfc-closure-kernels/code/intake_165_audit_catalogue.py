"""Read-only batch165 catalogue/placement audit, adapted from batch163.

--catalogue-root permits scratch preview texts. --preview explicitly permits
WRITE165SHA; final audits require the actual reconciliation commit. No supplied
verifier, proof compiler, version query, manifest interpretation or build runs.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import io
import json
import re
import subprocess
import zipfile

REPORTS = Path('SetTheory/Cardinals/docs/reports')
HOST = REPORTS / 'set-theory/zfc-closure-kernels'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--catalogue-root', type=Path)
    parser.add_argument('--write-sha', default='WRITE165SHA')
    parser.add_argument('--preview', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert __debug__, 'Keep assertions enabled.'
    repo = args.repo.resolve()
    catalogue = args.catalogue_root.resolve() if args.catalogue_root else repo
    assert not args.output.resolve().is_relative_to(repo), 'Evidence output must be external.'
    assert not args.output.exists(), 'Do not overwrite a previous audit.'
    git = lambda *command: subprocess.check_output(['git', '-C', str(repo), *command])

    def authored(relative):
        path = catalogue / relative
        return path if path.exists() else repo / relative

    tex = authored(REPORTS / 'manifest.tex').read_text()

    def escaped(i):
        n, i = 0, i - 1
        while i >= 0 and tex[i] == '\\':
            n, i = n + 1, i - 1
        return n % 2 == 1

    def group(pos):
        while tex[pos].isspace():
            pos += 1
        assert tex[pos] == '{'
        start, depth, pos = pos + 1, 1, pos + 1
        while depth:
            if tex[pos] in '{}' and not escaped(pos):
                depth += 1 if tex[pos] == '{' else -1
            pos += 1
        return tex[start:pos - 1], pos

    entries = []
    for match in re.finditer(r'^\\entry\s*(?=\{)', tex, re.M):
        pos, entry = match.end(), []
        for _ in range(5):
            value, pos = group(pos)
            entry.append(value)
        entry[1] = entry[1].replace('\\', '')
        entry[2] = entry[2].replace('\\', '')
        entries.append(entry)
    assert len(entries) == 290
    paths = [x[1] for x in entries]
    assert len(set(paths)) == 290
    assert all((repo / REPORTS / x[1] / x[2]).is_file() for x in entries)
    categories = Counter(x.split('/')[0] for x in paths)
    readme = authored(REPORTS / 'README.md').read_text()
    counts = {m.group(1): int(m.group(2)) for m in re.finditer(r'^\| \[`([^`]+)/`\].*\| (\d+) \|$', readme, re.M)}
    assert dict(categories) == counts and sum(counts.values()) == 290
    tracked = git('ls-files', '-z', '--', str(REPORTS)).decode().split('\0')
    root = repo / REPORTS
    artifacts = {(repo / x).parent for x in tracked if x and Path(x).suffix in ('.tex', '.pdf')
                 and len((repo / x).relative_to(root).parts) > 1
                 and (repo / x).relative_to(root).parts[0] in categories}
    minimal = {x for x in artifacts if not any(parent in artifacts for parent in x.parents if parent != root)}
    normalized = {x.parent if x.name in ('article', 'figures') and (x.parent / 'README.md').is_file() else x for x in minimal}
    assert {str(x.relative_to(root)) for x in normalized} == set(paths)

    incoming = authored(Path('docs/incoming/README.md')).read_text()
    rows = re.findall(r'^\| (\d+) \|', incoming, re.M)
    assert len(rows) == len(set(rows)) and rows[-1] == '165'
    assert 'Sixty-nine manuscripts' in tex
    assert 'sixty-nine manuscripts' in authored(HOST / 'README.md').read_text()
    assert all('500381f8f1' in value for value in (tex, readme, incoming))
    if not args.preview:
        assert re.fullmatch(r'[0-9a-f]{10,40}', args.write_sha)
        assert all('WRITE165SHA' not in value and args.write_sha in value for value in (tex, readme, incoming))
        git('cat-file', '-e', args.write_sha + '^{commit}')
    else:
        assert args.write_sha == 'WRITE165SHA' or re.fullmatch(r'[0-9a-f]{10,40}', args.write_sha)

    host = repo / HOST
    prefixes = {int(m.group(1)) for path in host.rglob('*') if path.is_file() and (m := re.match(r'^(\d{2})-', path.name))}
    assert set(range(1, 70)).issubset(prefixes)
    mapping = json.loads((host / 'data/intake-165-placement.json').read_text())
    assert mapping['batch'] == 165 and mapping['host_source'] == 69
    placed = [x for x in mapping['files'] if x['disposition'] == 'place_unchanged']
    archived = [x for x in mapping['files'] if x['disposition'] == 'archive_only']
    assert (len(placed), len(archived), len(mapping['files'])) == (454, 12, 466)
    package = mapping['archive']
    assert not (repo / package['archive']).exists()
    raw = git('show', package['first_arrival']['commit'] + ':' + package['archive'])
    assert hashlib.sha256(raw).hexdigest() == package['sha256']
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        payloads = {x['archive_member']: archive.read(x['archive_member']) for x in mapping['files']}
    for x in mapping['files']:
        assert hashlib.sha256(payloads[x['archive_member']]).hexdigest() == x['sha256']
        if x['disposition'] == 'place_unchanged':
            assert (repo / x['target']).read_bytes() == payloads[x['archive_member']]
            assert git('show', '500381f8f1:' + x['target']) == payloads[x['archive_member']]
    duplicate_path = 'docs/incoming/zfc245-proof-20261018.zip'
    original = git('show', '8286787dd0468d848db345debe304b002d7064a4:'+duplicate_path)
    repeated = git('show', '8e1d867deb:'+duplicate_path)
    assert original == repeated and not (repo / duplicate_path).exists()
    original_placement = '46e8518e0eddc4bc16a7a1b38cd21bd58abf9226'
    original_tree = git('ls-tree', '-r', '-z', original_placement, '--', str(HOST)).decode().split('\0')
    with zipfile.ZipFile(io.BytesIO(original)) as archive:
        blobs = {hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest():b
                 for i in archive.infolist() if not i.is_dir() for b in [archive.read(i)]}
    old_rows = [row.split('\t', 1) for row in original_tree if row and Path(row.split('\t',1)[1]).name.startswith('68-')]
    assert len(old_rows) == 273
    for left,path in old_rows:
        oid=left.split()[2];assert oid in blobs and git('show',original_placement+':'+path)==blobs[oid]
    # Queue evolves independently. Pin the eighteen paths recorded at placement,
    # but permit later committed arrivals without inventing new intake numbers.
    queue=json.loads((host/'data/intake-165-queue-supplement.json').read_text())
    assert queue['current_pending_count']==18
    for q in queue['current_pending']:
        assert (repo/q['path']).is_file()
        assert git('hash-object','--no-filters','--',str(repo/q['path'])).decode().strip()==q['git_blob']
    for name in ['intake-165.md', 'intake-165-reproduction.md']:
        text = (host / name).read_text()
        assert 'PENDING' not in text
        for link in re.findall(r'\]\(([^)]+)\)', text):
            assert ' ' not in link and (host / link).exists(), (name, link)
    assert (host / 'article.tex').read_bytes() == git('show', '500381f8f1:' + str(HOST / 'article.tex'))
    recovery = json.loads((host / 'data/intake-165-recovery.json').read_text())
    assert recovery['status'] == 'RECOVERED_AND_PLACED_BYTES_MATCH'
    assert recovery['files_recovered'] == 466 and recovery['placed_pairs_compared'] == 454
    main = json.loads((host/'data/intake-165-source69-main-execution.json').read_text())
    supp = json.loads((host/'data/intake-165-source69-supplemental-execution.json').read_text())
    assert main['status']=='PASS' and main['exit_code']==0 and not main['timed_out']
    assert len(main['summary']['jobs'])==14 and all(x['status']=='PASS' for x in main['summary']['jobs'])
    assert supp['status']=='PASS' and len(supp['records'])==8
    assert all(x['status']=='PASS' and x['exit_code']==0 and not x['timed_out'] for x in supp['records'])
    record = dict(status='PREVIEW_PASS' if args.preview else 'PASS', batch=165,
                  placement='500381f8f1', write=args.write_sha,
                  collection_reports=290, all_catalogued_roots_match=True,
                  categories=dict(categories), host_sources=69,
                  placed=454, archive_only=12, recovered=466,
                  source_archive_and_exact_duplicate_retired_and_recoverable=True,
                  duplicate_original_ancillary_blobs=273,
                  eighteen_recorded_later_arrivals_kept_queued=True,
                  base_article_unchanged=True, main_jobs=14, supplemental_jobs=8,
                  proof_compiler_calls=0, pdf_build_or_visual_review_claimed=False,
                  scope='Catalogue structure, exact original/placed bytes, links and result scopes; no supplied verifier replay or delivery-manifest interpretation.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
