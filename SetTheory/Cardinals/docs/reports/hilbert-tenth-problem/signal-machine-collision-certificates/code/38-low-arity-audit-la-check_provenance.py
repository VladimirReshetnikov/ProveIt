#!/usr/bin/env python3
"""Read-only preservation/provenance audit; portable source checks separate from local origin checks."""
import argparse,hashlib,json,stat
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main(a):
 src=a.source.resolve();out=a.out.resolve();assert src!=out and src not in out.parents
 result={'dependency_origin_checks':[]}
 for pin in json.loads((src/'SOURCE_PINS.json').read_text()):
  q=Path(pin['origin']);assert q.read_bytes()==(src/pin['file']).read_bytes();result['dependency_origin_checks'].append({'origin':str(q),'sha256':sha(q)})
 before=json.loads((src/'evidence/source_before.json').read_text());after=json.loads((src/'evidence/source_after.json').read_text())
 changes=[{'before':x,'after':y} for x,y in zip(before,after) if x!=y]
 assert len(before)==len(after)==912 and len(changes)==17
 assert changes==json.loads((src/'evidence/concurrent_source_changes.json').read_text())
 assert all('/report68-gap-statistics-release-20261004' in c['before']['path'] for c in changes)
 result['historical_changed_entries']=17;result['historical_changes_confined_to_report68']=True
 p0=json.loads((src/'evidence/report68_postseal_before.json').read_text());p1=json.loads((src/'evidence/report68_postseal_after.json').read_text());assert p0==p1 and len(p0)==332
 report=Path(p0[0]['path']);mf=report/'RELEASE_MANIFEST.json';assert sha(mf)=='2a95eb0ba3f1f7bd2e53de2b0595d5b2439de11bc3c6b5925f15d63046f98493'
 manifest=json.loads(mf.read_text());result['report68_manifest_sha256']=sha(mf)
 for rel,x in manifest['files'].items():
  p=report/rel;s=p.stat();assert p.is_file() and sha(p)==x['sha256'] and s.st_size==x['bytes'] and stat.S_IMODE(s.st_mode)==x['mode'] and s.st_mtime_ns==x['mtime_ns']
 for rel,x in manifest['directories'].items():
  p=report/rel;s=p.stat();assert p.is_dir() and stat.S_IMODE(s.st_mode)==x['mode'] and s.st_mtime_ns==x['mtime_ns']
 result['report68_manifest_files']=len(manifest['files']);result['report68_manifest_directories']=len(manifest['directories'])
 for x in p1:
  q=Path(x['path']);s=q.stat();assert s.st_mode==x['mode'] and s.st_mtime_ns==x['mtime_ns'] and s.st_size==x['size']
  if not x['is_dir']:assert sha(q)==x['sha256']
 result['report68_postseal_baseline_current_matches']=len(p1)
 receipt=report.parent/'report68-final-release-receipt.json';assert sha(receipt)=='d1781eeedb6f253e5e3a90551bd878c202d60ed4266619c7ceb61545d259240e'
 result['report68_receipt_sha256']=sha(receipt)
 out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='dependency_origin_checks'}))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',required=True,type=Path);p.add_argument('--out',required=True,type=Path);main(p.parse_args())
