#!/usr/bin/env python3
"""Bounded read-only assessment of one recorded producer and direct imports."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
R=ROOT/'Computability/DiophantineConsistency/research'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs={
 'trace75-bfs-ipra-final-assembly-plan/observations/attempt01/result.json':'b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c',
 'trace75-graph-support-331-inventory/observations/attempt02/stdout':'8a4748cf03711674ff0c1c6d14f7703afbd7f4f08673a2c4aed67ec32822537d',
 'direct-bfs-lean-row-transfer-prototype/observations/directbfsrowtransfer-attempt02/terminal.json':'49930da81109d9d72363a4e2d5b8bc01101d5284274a8f7dc46981044b890cdd',
 'direct-bfs-lean-row-transfer-prototype/observations/directbfsrowtransfer-attempt02/source.txt':'d081b4eb8e3be90a6fdf564f788ec6d01266d6873b4e7dfa824526d432fde964',
 'direct-bfs-lean-row-transfer-prototype/DirectBFSRowTransfer.lean':'d081b4eb8e3be90a6fdf564f788ec6d01266d6873b4e7dfa824526d432fde964',
 'direct-bfs-lean-row-transfer-prototype/observations/directbfsrowtransfer-attempt02/stdout':'90ff2a2837d6aee27e58f59eb1c4e4668174eba97e5ec4cf8bcf123aa0c0a2ef',
 'direct-bfs-lean-row-transfer-prototype/observations/directbfsrowtransfer-attempt02/stderr':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 'direct-bfs-lean-row-transfer-prototype/run-v2.py':'49bfe0832aab6cca9586e74ee4dba173871a3dc63df49eba141e9ff3726440ee'}
for p,h in inputs.items():assert sha(R/p)==h
keys=list(inputs);f=json.loads((R/keys[0]).read_text());inventory=json.loads((R/keys[1]).read_text());r=json.loads((R/keys[2]).read_text())
n='DirectBFSRowTransfer';assert n in inventory['direct_outside_project'];assert r['exit']==0
assert r['pins']['source']==r['after']['source']==inputs[keys[3]]
assert r['pins']['runner']==r['after']['runner']==inputs[keys[7]]
assert r['stdout_sha256']==inputs[keys[5]] and r['stderr_sha256']==inputs[keys[6]]
src=Path(r['command'][5]);out=Path(r['command'][7]);sel=f['selected_project'][n]['.olean']
assert src.name==n+'.lean' and out.name==n+'.olean'
assert sha(src)==inputs[keys[3]] and str(out.resolve())==sel['resolved']
assert sha(out)==r['object_sha256']==sel['sha256']
assert r['direct_imports']==r['direct_imports_after'];assert set(f['serialized_headers'][n])-{'Init'}=={x['module'] for x in r['direct_imports']}
compared=[]
for d in r['direct_imports']:
 p=Path(d['path']);s=f['selected_project'][d['module']]['.olean'];assert sha(p)==d['sha256']==s['sha256']==sha(s['resolved'])
 compared.append({'module':d['module'],'recorded_path':str(p),'current_recorded_realpath':str(p.resolve()),'selected_path':s['path'],'selected_realpath':s['resolved'],'same_realpath':str(p.resolve())==s['resolved'],'recorded_and_selected_sha256':d['sha256']})
for p,h in inputs.items():assert sha(R/p)==h
assert sha(src)==inputs[keys[3]] and sha(out)==sel['sha256']
for d in compared:assert sha(d['recorded_path'])==sha(d['selected_realpath'])==d['recorded_and_selected_sha256']
print(json.dumps({'status':'PASS','scope':'Bounded receipt and current source/object/direct .olean comparison. No atomic producer-time inputs, Init companions, dynamic imports, or transitive and package provenance claim.','inputs':inputs,'module':n,'receipt_source':str(src),'receipt_source_sha256':sha(src),'selected_object':sel,'recorded_exit':r['exit'],'header':f['serialized_headers'][n],'direct_imports':compared},indent=2,sort_keys=True))
