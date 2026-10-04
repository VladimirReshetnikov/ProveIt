"""Fresh static file hashing only. Does not import or execute source programs."""
from pathlib import Path
import hashlib
import json
import stat
import sys
from datetime import datetime, timezone
BASE = Path('/workspace/shared/radius-frontier-20261004')
OUT = Path('/workspace/shared/short-exactness-radius-20261004/evidence')
LIVE = Path('/workspace/shared/report70-two-scale-radius-release-20261004')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def state(roots):
    paths = []
    for root in roots:
        paths.append(root)
        if root.is_dir():
            paths.extend(root.rglob('*'))
    result = {}
    for p in sorted(set(paths)):
        s = p.lstat()
        item = {'mode': oct(stat.S_IMODE(s.st_mode)), 'mtime_ns': s.st_mtime_ns}
        if p.is_symlink():
            raise RuntimeError('Unexpected symlink: '+str(p))
        if p.is_file():
            item.update(bytes=s.st_size, sha256=digest(p))
        elif not p.is_dir():
            raise RuntimeError('Unexpected special file: '+str(p))
        result[str(p)] = item
    return result

stage = sys.argv[1]
if stage not in ('before', 'after'):
    raise ValueError(stage)
pins = {
    BASE/'proof-packet/manifest.json': 'f1c19ca86641cbf5ebaed81d0c78e82563258753bbf8f38f2f46229247b71fa0',
    BASE/'fresh-audit-static/AUDIT_MANIFEST.json': '3bfe65db1ad9c0aab9fd13641cfbad843a292d2c2dbec444fa0f7ebb856876b1',
}
for path, expected in pins.items():
    if digest(path) != expected:
        raise RuntimeError('Trusted manifest mismatch: '+str(path))
packet_manifest = json.loads((BASE/'proof-packet/manifest.json').read_text())
for rel, entry in packet_manifest['files'].items():
    p = BASE/'proof-packet'/rel
    if p.stat().st_size != entry['bytes'] or digest(p) != entry['sha256']:
        raise RuntimeError('Packet file mismatch: '+rel)
audit_manifest = json.loads((BASE/'fresh-audit-static/AUDIT_MANIFEST.json').read_text())
for rel, entry in audit_manifest['files'].items():
    p = BASE/rel
    s = p.stat()
    if s.st_size != entry['bytes'] or digest(p) != entry['sha256']:
        raise RuntimeError('Audit file mismatch: '+rel)
    if oct(stat.S_IMODE(s.st_mode)) != entry['mode_octal'] or s.st_mtime_ns != entry['mtime_ns']:
        raise RuntimeError('Audit metadata mismatch: '+rel)
roots = [BASE/'proof-packet', BASE/'fresh-audit-static', BASE/'fresh-audit-radius2',
         BASE/'two-scale-recognition-proof-packet-20261004.zip', BASE/'proof-packet-freeze-receipt.json']
result = {
    'timestamp_utc': datetime.now(timezone.utc).isoformat(),
    'stage': stage,
    'trusted_manifest_pins_verified': {str(k):v for k,v in pins.items()},
    'packet_entries_verified': len(packet_manifest['files']),
    'audit_entries_verified': len(audit_manifest['files']),
    'frozen_inputs': state(roots),
    'separately_observed_live_report70': state([LIVE]),
}
(OUT/(stage+'.json')).write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
if stage == 'after':
    before=json.loads((OUT/'before.json').read_text())
    changes={}
    for category in ('frozen_inputs','separately_observed_live_report70'):
        a,b=before[category],result[category]
        changes[category] = {k:{'before':a.get(k),'after':b.get(k)} for k in sorted(set(a)|set(b)) if a.get(k)!=b.get(k)}
    receipt={'before_utc':before['timestamp_utc'],'after_utc':result['timestamp_utc'],
             'frozen_inputs_unchanged':not changes['frozen_inputs'],
             'changes':changes,
             'scope':'Endpoint snapshots only; no continuous-static-interval claim. Source reads may update atime, which is outside the requested preservation scope.'}
    (OUT/'preservation-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    if changes['frozen_inputs']:
        raise RuntimeError('Frozen inputs changed')
print(json.dumps({'stage':stage,'packet_entries':len(packet_manifest['files']),'audit_entries':len(audit_manifest['files']),'frozen_snapshot_entries':len(result['frozen_inputs']),'live_report70_snapshot_entries':len(result['separately_observed_live_report70'])}))
