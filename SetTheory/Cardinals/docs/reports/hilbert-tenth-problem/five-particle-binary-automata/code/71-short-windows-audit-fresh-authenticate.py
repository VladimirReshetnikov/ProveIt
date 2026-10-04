"""Fresh read-only archive/hash/JSON verification. No inherited code is imported.

Only this audit directory is written. No source program or simulator is run.
"""
from pathlib import Path, PurePosixPath
from datetime import datetime, timezone
import hashlib
import io
import json
import stat
import sys
import zipfile

OUT = Path(__file__).resolve().parent
NEW = Path('/workspace/shared/short-exactness-radius-20261004')
OLD = Path('/workspace/shared/radius-frontier-20261004')
LIVE = Path('/workspace/shared/report70-two-scale-radius-release-20261004')
PINS = {
    NEW/'proof-packet/manifest.json': '72f8024c49a364bfd26ccc9f0e89d128e4390c1bf045477aa3d584bba3eaea31',
    NEW/'short-exactness-proof-packet-20261004.zip': '9bb5e63a780770689a5b7d353a130dee7535330e021202201d5c751d62601d37',
    OLD/'proof-packet/manifest.json': 'f1c19ca86641cbf5ebaed81d0c78e82563258753bbf8f38f2f46229247b71fa0',
    OLD/'fresh-audit-static/AUDIT_MANIFEST.json': '3bfe65db1ad9c0aab9fd13641cfbad843a292d2c2dbec444fa0f7ebb856876b1',
    OLD/'two-scale-recognition-proof-packet-20261004.zip': 'a3739bdd0d9015ea4c69f3a0b8b8fb6f0bd6828a6aa5251a08e902a1ca3d04b6',
    OLD/'proof-packet/original/report26.zip': '20a23b1ee22aed461942da4def6bade2bd55d777fce1fe49b6ff83248b7442e4',
}

def must(value, label):
    if not value:
        raise RuntimeError(label)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def pairs(items):
    result = {}
    for key, value in items:
        must(key not in result, 'Duplicate JSON key: '+key)
        result[key] = value
    return result

def js(data):
    return json.loads(data, object_pairs_hook=pairs)

def safe(name):
    p = PurePosixPath(name)
    must(not p.is_absolute() and '..' not in p.parts and '\\' not in name,
         'Unsafe relative name: '+name)
    return p

def checked(data, entry, label):
    if isinstance(entry, str):
        must(sha(data) == entry, 'Digest: '+label)
    else:
        must(len(data) == entry['bytes'] and sha(data) == entry['sha256'],
             'Size or digest: '+label)

def archive(data):
    result = {}
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for member in z.infolist():
            safe(member.filename)
            must(member.filename not in result, 'Duplicate ZIP member')
            must(not stat.S_ISLNK(member.external_attr >> 16), 'ZIP symlink')
            must(not member.is_dir(), 'Unexpected ZIP directory')
            result[member.filename] = z.read(member)
    return result

def inventory(root, manifest, metadata=False):
    for rel, entry in manifest['files'].items():
        safe(rel)
        p = root/rel
        checked(p.read_bytes(), entry, str(p))
        if metadata:
            s = p.lstat()
            must(oct(stat.S_IMODE(s.st_mode)) == entry['mode_octal'], 'Mode: '+str(p))
            must(s.st_mtime_ns == entry['mtime_ns'], 'Mtime: '+str(p))
    return len(manifest['files'])

def snapshot(roots):
    found = {}
    for root in roots:
        must(root.exists(), 'Missing source: '+str(root))
        entries = [root] + (list(root.rglob('*')) if root.is_dir() else [])
        for p in sorted(entries):
            s = p.lstat()
            must(not p.is_symlink(), 'Source symlink: '+str(p))
            item = {'mode_octal': oct(stat.S_IMODE(s.st_mode)), 'mtime_ns': s.st_mtime_ns}
            if stat.S_ISDIR(s.st_mode):
                item['type'] = 'directory'
            else:
                must(stat.S_ISREG(s.st_mode), 'Special source file')
                data = p.read_bytes()
                item.update(type='file', bytes=len(data), sha256=sha(data))
                after = p.lstat()
                must(s.st_mtime_ns == after.st_mtime_ns and s.st_size == after.st_size,
                     'File changed during read: '+str(p))
            found[str(p)] = item
    return found

def changes(a, b):
    return {p: {'before': a.get(p), 'after': b.get(p)}
            for p in sorted(set(a)|set(b)) if a.get(p) != b.get(p)}

stage = sys.argv[1]
must(stage in ('before', 'after'), 'Stage must be before or after')
start = datetime.now(timezone.utc).isoformat()
for p, digest in PINS.items():
    must(sha(p.read_bytes()) == digest, 'Pinned digest: '+str(p))

nm = js((NEW/'proof-packet/manifest.json').read_bytes())
om = js((OLD/'proof-packet/manifest.json').read_bytes())
am = js((OLD/'fresh-audit-static/AUDIT_MANIFEST.json').read_bytes())
counts = {
    'new_packet_entries': inventory(NEW/'proof-packet', nm, True),
    'predecessor_packet_entries': inventory(OLD/'proof-packet', om),
    'accepted_audit_entries': inventory(OLD, am, True),
}
for directory, manifest, zip_path, prefix in (
    (NEW/'proof-packet', nm, NEW/'short-exactness-proof-packet-20261004.zip', 'proof-packet/'),
    (OLD/'proof-packet', om, OLD/'two-scale-recognition-proof-packet-20261004.zip', 'two-scale-recognition-proof-packet/'),
):
    files = archive(zip_path.read_bytes())
    expected = set(manifest['files'])|{'manifest.json'}
    must(set(files) == {prefix+s for s in expected}, 'ZIP exact inventory')
    disk = {str(p.relative_to(directory)) for p in directory.rglob('*') if p.is_file()}
    must(disk == expected, 'Extracted exact inventory')
    for rel in expected:
        must(files[prefix+rel] == (directory/rel).read_bytes(), 'ZIP roundtrip: '+rel)

files26 = archive((OLD/'proof-packet/original/report26.zip').read_bytes())
prefix26 = 'parallel-involution-report26/'
release = js(files26[prefix26+'release-manifest.json'])
expected26 = set(release['files'])|{'release-manifest.json', 'release-manifest.json.sha256'}
must(set(files26) == {prefix26+s for s in expected26}, 'Report26 exact archive inventory')
for rel, entry in release['files'].items():
    checked(files26[prefix26+rel], entry, rel)
must(files26[prefix26+'release-manifest.json.sha256'].decode().split()[0]
     == sha(files26[prefix26+'release-manifest.json']), 'Release manifest digest line')
pins26 = js(files26[prefix26+'source-pins.json'])
for rel, entry in pins26['files'].items():
    checked(files26[prefix26+rel], entry, rel)
sci26 = js(files26[prefix26+'scientific/manifest.json'])
for rel, entry in sci26['files'].items():
    checked(files26[prefix26+'scientific/'+rel], entry, rel)
sums = files26[prefix26+'scientific/SHA256SUMS'].decode().splitlines()
for line in sums:
    digest, rel = line.split(maxsplit=1)
    rel = rel.lstrip('*')
    checked(files26[prefix26+'scientific/'+rel], digest, rel)
counts.update(report26_archive_files=len(files26), report26_release_entries=len(release['files']),
              report26_source_pins=len(pins26['files']), report26_scientific_entries=len(sci26['files']),
              report26_sha256sum_lines=len(sums))

origins = js((NEW/'proof-packet/dependency-origins.json').read_bytes())
for name, origin in origins.items():
    copied = (NEW/'proof-packet/dependencies'/name).read_bytes()
    checked(copied, origin, name)
    if 'source' in origin:
        source = Path(origin['source']).read_bytes()
    else:
        source_archive = Path(origin['source_archive']).read_bytes()
        must(sha(source_archive) == origin['archive_sha256'], 'Origin archive pin')
        source = archive(source_archive)[origin['member']]
    must(copied == source, 'Copied dependency origin: '+name)
counts['new_dependency_origins'] = len(origins)

old_copy_map = {
    'COMPILER_PROOF.md': 'scientific/COMPILER_PROOF.md', 'PROOF.md': 'scientific/PROOF.md',
    'audit-preservation.md': 'scientific/audit-preservation.md',
    'prior-art-audit.md': 'references/prior-art-audit.md', 'release-manifest.json': 'release-manifest.json',
    'report19-audit-universal-count.json': 'references/report19-audit-universal-count.json',
    'report19-universal-receipt.json': 'references/report19-universal-receipt.json',
    'resource-ledger.json': 'scientific/resource-ledger.json', 'source-pins.json': 'source-pins.json',
}
for copied, source in old_copy_map.items():
    must((OLD/'proof-packet/dependencies'/copied).read_bytes() == files26[prefix26+source],
         'Predecessor copied dependency: '+copied)
counts['predecessor_dependency_origins'] = len(old_copy_map)
universal = js((NEW/'proof-packet/dependencies/report19-universal-receipt.json').read_bytes())['source_sha256']
must(all(sha(data) != universal for data in files26.values()), 'Unexpected universal source table')

hb = js((NEW/'proof-packet/evidence/before.json').read_bytes())
ha = js((NEW/'proof-packet/evidence/after.json').read_bytes())
hr = js((NEW/'proof-packet/evidence/preservation-receipt.json').read_bytes())
historical = {k: changes(hb[k], ha[k]) for k in ('frozen_inputs', 'separately_observed_live_report70')}
must(historical == hr['changes'], 'Historical preservation delta')
must(not historical['frozen_inputs'], 'Historical frozen inputs changed')
counts['historical_frozen_entries'] = len(hb['frozen_inputs'])
counts['historical_live_added_entries'] = sum(v['before'] is None for v in historical['separately_observed_live_report70'].values())
counts['historical_live_changed_existing_entries'] = sum(v['before'] is not None for v in historical['separately_observed_live_report70'].values())

roots = [NEW/'proof-packet', NEW/'short-exactness-proof-packet-20261004.zip', NEW/'seal-receipt.json',
         OLD/'proof-packet', OLD/'fresh-audit-static', OLD/'fresh-audit-radius2',
         OLD/'two-scale-recognition-proof-packet-20261004.zip', OLD/'proof-packet-freeze-receipt.json',
         OLD/'archive', OLD/'inert']
result = {'stage': stage, 'started_utc': start, 'finished_utc': datetime.now(timezone.utc).isoformat(),
          'pins': {str(p): d for p,d in PINS.items()}, 'counts': counts,
          'frozen_inputs': snapshot(roots), 'live_report70': snapshot([LIVE]),
          'historical_preservation_delta_verified': True,
          'universal_source_table_not_in_report26_zip': True,
          'scope': 'Read-only bytes, metadata and object-set endpoint observations; atimes excluded; not continuous immutability.'}
result['finished_utc'] = datetime.now(timezone.utc).isoformat()
(OUT/(stage+'.json')).write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
if stage == 'after':
    before = js((OUT/'before.json').read_bytes())
    delta = {k: changes(before[k], result[k]) for k in ('frozen_inputs', 'live_report70')}
    receipt = {'before_utc': before['started_utc'], 'after_utc': result['finished_utc'],
               'changes': delta, 'frozen_unchanged': not delta['frozen_inputs'],
               'live_unchanged_in_this_audit_interval': not delta['live_report70'],
               'historical_live_change_qualification_retained': counts,
               'scope': result['scope']}
    (OUT/'preservation.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    must(not delta['frozen_inputs'], 'Frozen audit inputs changed')
print(json.dumps({'stage': stage, 'status': 'PASS', 'counts': counts,
                  'frozen_snapshot_entries': len(result['frozen_inputs']),
                  'live_snapshot_entries': len(result['live_report70'])}, sort_keys=True))
