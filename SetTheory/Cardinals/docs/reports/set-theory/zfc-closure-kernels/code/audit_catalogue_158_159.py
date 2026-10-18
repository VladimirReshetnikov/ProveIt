"""Read-only catalogue/map audit for batches 158–159 and the 56-source host.

By default require final write metadata. --catalogue-root permits catalogue
source previews; --preview defers only the write-commit placeholder check.
Read archive payloads and placed bytes directly, never checksum manifests.
No delivered code, proof compiler, build or search is executed. Output is
written only to external scratch.
"""
from pathlib import Path, PurePosixPath
from collections import Counter
import argparse
import io
import json
import re
import struct
import subprocess
import tempfile
import zipfile
import zlib


REPORTS = Path('SetTheory/Cardinals/docs/reports')
HOST = REPORTS / 'set-theory/zfc-closure-kernels'
PLACEMENTS = {158: '78b528440a', 159: '901dd50056'}
# source: batch, slug, arrival, archive basename, original root, placed, archive-only
SOURCES = {
    51: (158, 'geometric', 'e92db213bc6d74eca74856e9dc363d191b40df21',
         'zfc_geometric_counter_research_2026-10-17.zip', 'zfc_gap_clock', 110, 9),
    52: (158, 'roles', 'a2bf288dead95b653919b86608e3f2cca47552f7',
         'zfc_sub252_research_20261017.zip', 'zfc_sub252_research_20261017', 132, 4),
    53: (158, 'span', '073543e11b6b9bdd610ce8b56afd3c0a4aa054e4',
         'permutation252-reduction-study.zip', 'permutation252-reduction-study', 196, 10),
    54: (158, 'cachemp', '80e26b89e905bf3e5dfc322befdc1c6eaf25a109',
         'cachemp252_research_2026-10-17.zip', 'cachemp252-research-20261017', 216, 8),
    55: (158, 'countdown', '80e26b89e905bf3e5dfc322befdc1c6eaf25a109',
         'zfc252-reduction-research-2026-10-17.zip', 'zfc252-reduction-research-2026-10-17', 158, 3),
    56: (159, 'negation', '80e26b89e905bf3e5dfc322befdc1c6eaf25a109',
         'zfc-state-reduction-research.zip', 'zfc-state-reduction-research', 321, 6),
}


def relative(name):
    assert isinstance(name, str) and name and '\\' not in name and '\0' not in name
    p = PurePosixPath(name)
    assert p.parts and not p.is_absolute() and '..' not in p.parts
    assert ':' not in p.parts[0] and p.as_posix() == name.rstrip('/'), name
    return p


def payloads(raw, root, partial):
    """Read opaque archive files; the partial archive has local entries only."""
    members = []
    if not partial:
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for info in archive.infolist():
                members.append((info.filename, None if info.is_dir() else archive.read(info)))
    else:
        pos = 0
        while pos < len(raw):
            assert len(raw) - pos >= 30 and raw[pos:pos + 4] == b'PK\x03\x04', pos
            _, _, flags, method, _, _, _, csize, usize, nlen, xlen = struct.unpack_from('<4s5H3I2H', raw, pos)
            assert not flags & 9, 'Encryption/data descriptors unsupported'
            start = pos + 30 + nlen + xlen
            assert start + csize <= len(raw), 'Incomplete local payload'
            name = raw[pos + 30:pos + 30 + nlen].decode('utf-8' if flags & 0x800 else 'cp437')
            data = raw[start:start + csize]
            if method == 8:
                decoder = zlib.decompressobj(-15)
                data = decoder.decompress(data) + decoder.flush()
                assert decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail
            else:
                assert method == 0, method
            assert len(data) == usize
            members.append((name, None if name.endswith('/') else data))
            pos = start + csize
    seen = set()
    files = {}
    for name, data in members:
        p = relative(name)
        assert p.parts[0] == root and p.as_posix() not in seen, name
        seen.add(p.as_posix())
        if data is not None:
            assert len(p.parts) > 1
            files[PurePosixPath(*p.parts[1:]).as_posix()] = data
    return files


def main():
    if not __debug__:
        raise SystemExit('Keep assertions enabled.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path.cwd())
    parser.add_argument('--catalogue-root', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--preview', action='store_true')
    parser.add_argument('--write-commit', help='Optional exact expected write commit or unambiguous prefix.')
    args = parser.parse_args()
    repo = args.repo.resolve()
    cat = args.catalogue_root.resolve() if args.catalogue_root else repo
    root = repo / REPORTS
    host = repo / HOST
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-catalogue158-159-audit-'))
    if out.is_relative_to(repo):
        parser.error('External output directory required.')
    out.mkdir(parents=True, exist_ok=True)

    def git(*command):
        return subprocess.check_output(['git', *command], cwd=repo)

    assert Path(git('rev-parse', '--show-toplevel').decode().strip()).resolve() == repo
    tex = (cat / REPORTS / 'manifest.tex').read_text()

    def escaped(i):
        n = 0
        i -= 1
        while i >= 0 and tex[i] == '\\':
            n += 1
            i -= 1
        return n % 2 == 1

    def group(pos):
        while tex[pos].isspace():
            pos += 1
        assert tex[pos] == '{', (pos, tex[pos:pos + 80])
        start = pos + 1
        depth = 1
        pos += 1
        while depth:
            if tex[pos] in '{}' and not escaped(pos):
                depth += 1 if tex[pos] == '{' else -1
            pos += 1
        return tex[start:pos - 1], pos

    entries = []
    for match in re.finditer(r'^\\entry\s*(?=\{)', tex, re.M):
        pos = match.end()
        entry = []
        for _ in range(5):
            value, pos = group(pos)
            entry.append(value)
        entry[1] = entry[1].replace('\\', '')
        entry[2] = entry[2].replace('\\', '')
        entries.append(entry)
    assert len(entries) == 290
    paths = [x[1] for x in entries]
    assert len(set(paths)) == 290
    assert all((root / x[1] / x[2]).is_file() for x in entries)
    categories = Counter(x.split('/')[0] for x in paths)
    readme = (cat / REPORTS / 'README.md').read_text()
    counts = {m.group(1): int(m.group(2)) for m in re.finditer(r'^\| \[`([^`]+)/`\].*\| (\d+) \|$', readme, re.M)}
    assert dict(categories) == counts and sum(counts.values()) == 290
    tracked = git('ls-files', '-z', '--', str(REPORTS)).decode().split('\0')
    artifacts = {(repo / x).parent for x in tracked if x and Path(x).suffix in ('.tex', '.pdf')
                 and len((repo / x).relative_to(root).parts) > 1
                 and (repo / x).relative_to(root).parts[0] in categories}
    minimal = {x for x in artifacts if not any(parent in artifacts for parent in x.parents if parent != root)}
    normalized = {x.parent if x.name in ('article', 'figures') and (x.parent / 'README.md').is_file() else x for x in minimal}
    assert {str(x.relative_to(root)) for x in normalized} == set(paths)

    incoming = (cat / 'docs/incoming/README.md').read_text()
    rows = re.findall(r'^\| (\d+) \|', incoming, re.M)
    assert len(rows) == len(set(rows)) and rows[-2:] == ['158', '159']
    incoming_rows = {int(m.group(1)): m.group(0) for m in re.finditer(r'^\| (\d+) \|.*$', incoming, re.M)}
    assert 'Batches158–159 add' in readme and '{Fifty-six manuscripts reconciled' in tex
    assert 'fifty-six manuscripts' in (host / 'README.md').read_text().lower()
    assert 'preserve1133 ancillary files;40' in readme
    for batch, commit in PLACEMENTS.items():
        assert commit in readme and commit in incoming_rows[batch] and commit in tex
        assert git('cat-file', '-t', commit).strip() == b'commit'
    write_commit = None
    if not args.preview:
        assert 'WRITE158159_PENDING' not in incoming + readme + tex
        labels = []
        for batch in (158, 159):
            field = incoming_rows[batch].split('|')[3].strip()
            match = re.match(r'`([0-9a-f]{7,40})`:', field)
            assert match, (batch, field)
            labels.append(git('rev-parse', match.group(1) + '^{commit}').decode().strip())
            assert match.group(1) in readme
        assert labels[0] == labels[1]
        write_commit = labels[0]
        if args.write_commit:
            assert write_commit == git('rev-parse', args.write_commit + '^{commit}').decode().strip()
    prefixes = {int(m.group(1)) for file in host.rglob('*') if file.is_file()
                and (m := re.match(r'^(\d{2})-', file.name))}
    assert set(range(1, 57)).issubset(prefixes)

    maps = {batch: json.loads((host / f'data/intake-{batch}-placement.json').read_text()) for batch in (158, 159)}
    all_targets = []
    archives = []
    total_placed = total_archive_only = total_delivered = 0
    for batch, mapping in maps.items():
        assert mapping['batch'] == batch
        expected_sources = {n for n, spec in SOURCES.items() if spec[0] == batch}
        assert set(map(int, mapping['counts'])) == expected_sources
        manuscripts = {m['local_source']: m for m in mapping['manuscripts']}
        assert len(manuscripts) == len(mapping['manuscripts']) and set(manuscripts) == expected_sources
        assert {r['local_source'] for r in mapping['placements'] + mapping['archive_only']} == expected_sources
        for n in sorted(expected_sources):
            _, slug, arrival, name, original_root, placed_count, archive_count = SOURCES[n]
            archive_path = 'docs/incoming/' + name
            manuscript = manuscripts[n]
            assert manuscript['archive'] == archive_path and manuscript['arrival'] == arrival and manuscript['slug'] == slug
            assert mapping['counts'][str(n)] == {'staged': placed_count, 'archive_only': archive_count}
            placed = [r for r in mapping['placements'] if r['local_source'] == n]
            archived = [r for r in mapping['archive_only'] if r['local_source'] == n]
            assert len(placed) == placed_count and len(archived) == archive_count
            inventory = placed + archived
            names = [r['delivered'] for r in inventory]
            assert len(set(names)) == len(names)
            assert all(r['archive'] == archive_path and r['arrival'] == arrival for r in inventory)
            assert all('target' not in r for r in archived)
            raw = git('show', arrival + ':' + archive_path)
            files = payloads(raw, original_root, partial=n == 56)
            assert len(files) == placed_count + archive_count and set(files) == set(names)
            original_records = manuscript['files']
            assert len(original_records) == len(files) and {r['delivered'] for r in original_records} == set(files)
            for r in inventory:
                assert len(files[r['delivered']]) == r['bytes']
            for r in placed:
                target = relative(r['target'])
                assert target.is_relative_to(PurePosixPath(str(HOST)))
                path = repo / str(target)
                assert path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(host.resolve())
                assert path.name.startswith(f'{n:02d}-{slug}-'), path
                assert path.read_bytes() == files[r['delivered']], path
                all_targets.append(str(target))
            assert not (repo / archive_path).exists()
            assert not git('ls-files', '--', archive_path).strip()
            blob = git('rev-parse', arrival + ':' + archive_path).decode().strip()
            assert git('cat-file', '-t', blob).strip() == b'blob'
            assert name.replace('_', r'\_') in next(x[3] for x in entries if x[1] == 'set-theory/zfc-closure-kernels')
            assert arrival[:10] in tex
            archives.append(dict(source=n, batch=batch, arrival=arrival, path=archive_path,
                                 blob=blob, bytes=len(raw), recoverable=True, retired=True,
                                 placed_files=placed_count, archive_only_files=archive_count,
                                 recovered_members=len(files), partial_delivery=n == 56))
            total_placed += placed_count
            total_archive_only += archive_count
            total_delivered += len(files)
    assert len(all_targets) == len(set(all_targets)) == total_placed == 1133
    assert total_archive_only == 40 and total_delivered == 1173
    assert git('show', 'fab89c5d26:' + str(HOST / 'article.tex')) == (host / 'article.tex').read_bytes()
    result = dict(batches=[158, 159], status='PREVIEW_PASS' if args.preview else 'PASS',
                  preview=args.preview, repo=str(repo), catalogue_root=str(cat),
                  manifest_entries=290, unique_report_directories=290,
                  every_main_artifact_exists=True, all_tracked_artifact_roots_catalogued=True,
                  category_counts=counts, host_sources=56, all_prefixes_01_through_56_present=True,
                  incoming_numbered_rows_unique=True, last_incoming_batch=159,
                  placement_files=1133, available_delivered_files=1173, archive_only_files=40,
                  all_placed_bytes_match_archive_payloads=True, archives=archives,
                  placement_commits=PLACEMENTS, write_commit=write_commit,
                  base_article_unchanged=True, checksum_manifest_checks=False,
                  line_ending_work=False, compiler_invocations=0, delivered_code_executions=0,
                  scope='Catalogue structure, exact placement maps/payloads, Git archive recovery/retirement and base identity. Source56 is only the 327 available members, not a complete intended delivery. Preview defers the final write-commit check only.')
    (out / 'catalogue-audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
