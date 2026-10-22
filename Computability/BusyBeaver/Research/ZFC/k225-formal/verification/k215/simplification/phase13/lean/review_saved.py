"""Check phase13's saved evidence and pinned phase12 reference without Lean."""
from pathlib import Path
import argparse, json, tarfile
import packet

def review(directory, basis_repo, repo=None):
 directory = Path(directory); summary = json.loads((directory/'result.json').read_text()); index = json.loads((directory/'index.json').read_text()); members = {}
 assert summary['status'] == 'PASS_COLLECTED_PHASE13' and packet.sha(directory/'execution.tar.gz') == summary['archive_sha256'] and packet.sha(directory/'index.json') == summary['index_sha256']
 with tarfile.open(directory/'execution.tar.gz', 'r:gz') as stream:
  for item in stream:
   packet.safe(item.name); assert item.isfile() and item.name not in members
   data = stream.extractfile(item).read(); assert index[item.name] == {'sha256': packet.digest(data), 'bytes': len(data)}; members[item.name] = data
 assert packet.manifest(members) == index and len(members) == summary['archive_members']
 for name in ['basis.py', 'basis-reference.json', 'packet.py', 'review_saved.py', 'README.md']:
  assert (directory/name).read_bytes() == members['review/'+name]
 freeze = json.loads(members['review/freeze.json'])
 assert freeze['status'] == 'FROZEN_PUBLICATION_HELPERS_NOT_EXECUTED'
 for name, pin in freeze['files'].items(): assert packet.digest(members['review/'+name]) == pin
 checked = packet.validate(members, basis_repo, current_repo=repo)
 assert all(summary[k] == v for k, v in checked.items() if k not in {'status', 'current_sources_checked'})
 post = json.loads(members['review/live-postcheck.json']); assert post == summary['live_postcheck'] and post['status'] == 'PASS_LIVE_POSTCHECK'
 assert post['providers'] == {packet.MAIN: 187, packet.COMP: 70} and post['combined_project_sources'] == 199 and post['endpoint_audit_objects'] == 2
 assert post['all_live_sources_objects_logs_dependencies_rehashed'] and post['absence_gates'] == 2
 config = json.loads(members['review/config.json'])
 assert post['historical_inputs'] == config['historical_inputs'] and post['current_adoptions'] == packet.ADOPTIONS
 for root, label in [(packet.MAIN, 'execution'), (packet.COMP, 'compatibility')]:
  before = json.loads(members[label+'/before.json']); assert post['before_input_counts'][root] == len(before['inputs'])
 return {**checked, 'status': 'PASS_SAVED_PHASE13', 'archive_sha256': summary['archive_sha256'], 'archive_members': len(members), 'reviewer_sha256': packet.sha(__file__), 'validator_sha256': packet.sha(Path(__file__).with_name('packet.py'))}

if __name__ == '__main__':
 parser = argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
 parser.add_argument('--basis-repo', type=Path, required=True); parser.add_argument('--repo', type=Path); parser.add_argument('--output', type=Path, required=True)
 args = parser.parse_args(); assert not args.output.exists()
 result = review(args.packet, args.basis_repo, args.repo); args.output.write_bytes(packet.dump(result)); print(json.dumps(result, indent=2))
