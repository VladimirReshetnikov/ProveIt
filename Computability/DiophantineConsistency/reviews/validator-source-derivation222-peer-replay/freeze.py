from pathlib import Path
import hashlib
import json
import shutil

SRC = Path('/tmp/validator-source-derivation222-peer-zt8k99i_')
REV = Path('/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/reviews')
DST = REV/'validator-source-derivation222-peer-replay'

def pin(p):
    return {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest(), 'bytes': p.stat().st_size}

state = json.loads((SRC/'state.json').read_text())
assert state['status'] == 'PASS' and len(state['records']) == 2
assert not DST.exists()
DST.mkdir()
for p in SRC.iterdir():
    if p.is_file() and not p.is_symlink():
        shutil.copy2(p, DST/p.name)
shutil.copy2(__file__, DST/'freeze.py')
manifest = [dict(path=p.name, sha256=pin(p)['sha256'], bytes=p.stat().st_size)
            for p in sorted(DST.iterdir()) if p.is_file()]
(DST/'FILES.json').write_text(json.dumps(manifest, indent=2)+'\n')
result = {
    'status': 'PASS', 'scope': state['scope'], 'private': str(SRC),
    'author_packet': pin(REV/'validator-source-derivation222-replay.json'),
    'author_receipt': pin(REV/'validator-source-derivation222-author.md'),
    'state': pin(DST/'state.json'), 'driver': pin(DST/'driver.py'),
    'inputs': pin(DST/'inputs.json'), 'observations': pin(DST/'observations.json'),
    'records': state['records'], 'actual_fresh_commands': 2,
    'counts': {'cached_custom': 164, 'Foundation': 117, 'cached_artifacts': 515,
               'external_boundaries': 40, 'axiom_reports': 17,
               'fresh_hash_observations': state['observation_count']},
    'manifest': pin(DST/'FILES.json'), 'bundle_files': len(manifest),
}
out = REV/'validator-source-derivation222-peer-replay.json'
assert not out.exists()
out.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'packet': pin(out), 'manifest': pin(DST/'FILES.json'),
                  'files': len(manifest)}, indent=2))
