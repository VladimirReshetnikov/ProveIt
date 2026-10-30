from pathlib import Path
import hashlib,json
new=json.loads(Path('/tmp/ha87-full-transitive-rpkdrhy_/state.json').read_text())['graph'];old=json.loads(Path('/tmp/ha87-full-transitive-u5x2_xjr/state.json').read_text())['graph']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
changed=[m for m in new['source_hashes'] if old['source_hashes'].get(m)!=new['source_hashes'][m]]
edge=[m for m in new['edges'] if old['edges'].get(m)!=new['edges'][m]]
bad=[m for m,p in new['sources'].items() if sha(p)!=new['source_hashes'][m]]
print('source changes:',changed);print('edge changes:',edge);print('postcheck drift:',bad)
assert not bad
