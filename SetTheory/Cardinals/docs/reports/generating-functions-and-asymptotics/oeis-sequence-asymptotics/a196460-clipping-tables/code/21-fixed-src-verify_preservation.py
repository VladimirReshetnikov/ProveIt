"""Compare the authentic broad snapshots and certify only the core boundary."""
import json
from pathlib import Path

base = Path(__file__).parent / 'evidence'
before = json.loads((base / 'input-before.json').read_text())
after = json.loads((base / 'input-current.json').read_text())
release_roots = ('/workspace/shared/report69-low-arity-compilers-release-20261004',
                 '/workspace/shared/report70-two-scale-radius-release-20261004')
def core(path):
    return not any(path == p or path.startswith(p + '/') for p in release_roots)

a = {p: v for p, v in before.items() if core(p)}
b = {p: v for p, v in after.items() if core(p)}
assert a == b
changed = [p for p in sorted(set(before) | set(after)) if before.get(p) != after.get(p)]
assert all(not core(p) for p in changed)
result = {'core_entries': len(a), 'core_bytes_modes_mtimes_unchanged': True,
          'broad_before_entries': len(before), 'broad_current_entries': len(after),
          'concurrent_release_differences': len(changed),
          'whole_release_interval_preservation_claimed': False}
with (base / 'preservation-result.json').open('x') as stream:
    json.dump(result, stream, indent=2)
    stream.write('\n')
print(json.dumps(result, sort_keys=True))
