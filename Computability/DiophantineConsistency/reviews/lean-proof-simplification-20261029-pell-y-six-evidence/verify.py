from pathlib import Path
import hashlib,json,subprocess
r=Path(__file__).resolve().parent; m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();review=r/m['independent_review']['path'];assert h(review.read_bytes())==m['independent_review']['sha256']
for phase,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
 info=m['source_snapshots'][phase];b=subprocess.check_output(['git','show',rev+':'+m['source_path']]);assert len(b)==info['bytes'] and h(b)==info['sha256'];p=Path(info['temporary_path']);assert p.read_bytes()==b
for path,meta in m['external_evidence'].items():
 p=Path(path);assert p.is_file(),f'external evidence unavailable: {path}';assert p.stat().st_size==meta['bytes'] and h(p.read_bytes())==meta['sha256'],path
print('PASS git snapshots, review and',len(m['external_evidence']),'external evidence hashes; full validation requires the external evidence')
