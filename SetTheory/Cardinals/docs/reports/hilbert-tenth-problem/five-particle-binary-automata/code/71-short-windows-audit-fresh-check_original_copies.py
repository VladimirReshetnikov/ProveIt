"""Fresh read-only authentication of recovered Report26 and historical states."""
from pathlib import Path
import hashlib
import json
import stat
import zipfile

OUT = Path(__file__).resolve().parent
BASE = Path('/workspace/shared/radius-frontier-20261004')
archive = BASE/'proof-packet/original/report26.zip'
recovered = BASE/'archive/Two_Parallel_Conservative_Involutions_Package.zip'
root = BASE/'inert/parallel-involution-report26'
historical = json.loads((BASE/'fresh-audit-static/original-state-before.json').read_text())
historical_after = json.loads((BASE/'fresh-audit-static/original-state-after.json').read_text())
if archive.read_bytes() != recovered.read_bytes():
    raise RuntimeError('Recovered archive mismatch')
with zipfile.ZipFile(archive) as z:
    archived = {n.removeprefix('parallel-involution-report26/') for n in z.namelist()}
    prefix = 'inert/parallel-involution-report26/'
    expected = {n.removeprefix(prefix) for n,entry in historical.items()
                if n.startswith(prefix) and entry['type'] == 'file'}
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    if actual != expected:
        raise RuntimeError('Recovered tree inventory mismatch')
    if not expected <= archived:
        raise RuntimeError('Recovered tree includes nonarchive files')
    for rel in expected:
        if z.read('parallel-involution-report26/'+rel) != (root/rel).read_bytes():
            raise RuntimeError('Recovered file mismatch: '+rel)
if historical != historical_after:
    raise RuntimeError('Prior audit original-state snapshots differ')
changed_since = {}
for rel, entry in historical.items():
    p = BASE/rel
    s = p.lstat()
    current = {'mode_octal':oct(stat.S_IMODE(s.st_mode)), 'mtime_ns':s.st_mtime_ns,
               'type':'directory' if p.is_dir() else 'file'}
    if p.is_file():
        data = p.read_bytes()
        current.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
    if current != entry:
        changed_since[rel] = {'historical':entry, 'current':current}
result = {'status':'PASS', 'archive_identity_verified':True,
          'recovered_report26_files_verified':len(expected),
          'inert_extraction_is_deliberately_partial':True,
          'archive_files_not_extracted':sorted(archived-expected),
          'prior_69_entry_preservation_snapshots_equal':historical == historical_after,
          'changes_since_prior_audit':changed_since,
          'no_inherited_program_executed':True}
(OUT/'original-copies.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','files':len(expected),'prior_entries':len(historical),
                  'changed_since_prior_audit':len(changed_since)},sort_keys=True))
