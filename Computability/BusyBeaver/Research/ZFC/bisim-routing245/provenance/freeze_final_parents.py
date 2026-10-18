"""Freeze existing complete parent evidence; never runs a guard or compiler."""
from pathlib import Path
import ast,difflib,hashlib,json
B=Path('/tmp/zfc-routing245-lean/source-bisim-production')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p.resolve()),sha256=h(p))
def main():
 manifest=B/'units-v2.json';assert h(manifest)=='a7a408f6d0d865d48e11b73adb6c4f58fb71b1311cf0a60b8b2e567753a1bb87'
 units={row['key']:row for row in json.loads(manifest.read_text())['units']}
 data=B/'data-run1/verification.json';assert h(data)=='64d0932251e46f3541cd5ccfa691452e199db7d8a4a66e9529ef96afc1bc9993'
 batches=[B/'chunk000-run1/batch.json',B/'chunks001-094-run1/batch.json'];combined=[]
 for batch in batches:
  record=json.loads(batch.read_text());assert record['status']=='PASS'and record['prepare_only']is False and record['failed_unit']is None
  combined.extend(record['completed_units'])
 assert [row['key']for row in combined]==[f'chunk{i:03}'for i in range(95)]
 chunks=[]
 for index,row in enumerate(combined):
  key=f'chunk{index:03}';path=Path(row['path']).resolve();assert row['status']=='PASS'and h(path)==row['sha256']
  record=json.loads(path.read_text());assert record['status']=='PASS'and record['prepare_only']is False
  assert record['named_axiom_probes']==1 and record['callers']==2 and record['only_standard_axioms']is True
  assert record['block_interval']==[32*index,min(32*index+32,3013)]and record['before']==record['after']
  assert record['source_object_recorded_before_audit']is True and record['all_fresh_objects_unchanged_after_audit']is True
  assert record['parent_evidence']==[desc(data)]
  assert [command['label']for command in record['commands']]==['source','audit']and all(command['exit_code']==0 and not command.get('timed_out',False)for command in record['commands'])
  for role in ['source','audit']:
   assert record[role]['sha256']==units[key][role]['sha256']==h(Path(record[role]['path']))==h(Path(record[role]['snapshot']))
  fresh=record['fresh_modules'];assert len(fresh)==1 and fresh[0]['module']==units[key]['module']and h(Path(fresh[0]['path']))==fresh[0]['sha256']
  saved=dict(record['source_pass_object']);saved.pop('source_command_index',None);assert saved==fresh[0]
  chunks.append(dict(key=key,record=desc(path)))
 parent_index=B/'final-parents.json';assert not parent_index.exists()
 parent_index.write_text(json.dumps(dict(schema='routing245-bisim-final-parents-v1',data=desc(data),manifest=desc(manifest),chunks=chunks,observed_complete_batches=[desc(p)for p in batches],status='ALL95_ACTUAL_PASS'),indent=2)+'\n')
 old=B/'check-final-pending.py';assert h(old)=='41f317bee7a72ac3679ea5a5698c387f69f86b436eefdc5fd373c53f517247ec'
 text=old.read_text();assert text.count("'parents': None")==1
 new=text.replace("'parents': None",repr('parents')+': '+repr(h(parent_index)))
 ast.parse(new);dest=B/'check-final.py';assert not dest.exists();dest.write_text(new)
 diff=B/'final-parent-freeze.diff';diff.write_text(''.join(difflib.unified_diff(text.splitlines(True),new.splitlines(True),fromfile=old.name,tofile=dest.name)))
 receipt=dict(status='SOURCE_ONLY_ALL95_PARENT_FREEZE',pending_guard=desc(old),guard=desc(dest),parent_index=desc(parent_index),actual_complete_chunk_records=95,exact_guard_change='One pending parent-index SHA replaced.',batches=[desc(p)for p in batches],compiler_execution=False,guard_execution=False)
 (B/'final-parent-freeze.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
