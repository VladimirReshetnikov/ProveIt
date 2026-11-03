#!/usr/bin/env python3
"""Inspect frozen author receipts and current direct object selection; no Lean replay."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2]; R=D/'research'
rows=[('direct-bfs-model-forward-word-prototype','DirectBFSModelForwardWord','directbfsmodelforwardword-attempt01',['DirectBFSModelForwardWord.forward_ne_one','DirectBFSModelForwardWord.original_cast','DirectBFSModelForwardWord.direct_forward_cast','DirectBFSModelForwardWord.transfer'],'daa46ed4caf332835006e168a7b468b0e2c452364a01440afea8e0595da45ad8'),('direct-bfs-halt-packed-word-prototype','DirectBFSHaltPackedWord','directbfshaltpackedword-attempt01',['DirectBFSHaltPackedWord.halt_packed_word'],'eafcbf541ff2e66504e55d1b2ff4204110688bb5571f377350a8fc06ef6e60ea'),('direct-bfs-halt-packed-pulse-prototype','DirectBFSHaltPackedPulse','directbfshaltpackedpulse-attempt01',['DirectBFSHaltPackedPulse.halt_packed_word'],'c46b4977182e3c99da18919af442bec94e9cb52dc1e177f0c484369cc8d55f80'),('direct-bfs-halt-packed-family-prototype','DirectBFSHaltPackedFamily','directbfshaltpackedfamily-attempt01',['DirectBFSHaltPackedFamily.halt_packed_family'],'911da1d0b5c0fd308e449a554879311f065533a83112c24319e718db3ebb1511'),('direct-bfs-conditional-packing-prototype','DirectBFSConditionalPacking','directbfsconditionalpack-attempt01',['DirectBFSConditionalPacking.pack_from_remaining_fields'],'3a265c1005a983fe2c9448ebfab855a648b259ea4c3c6b5562b66e1c3105dc11')]
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
for dirname,name,attempt,theorems,output in rows:
 p=R/dirname;s=p/(name+'.lean');run=p/'run.py';o=p/'observations'/attempt;rec=json.loads((o/'terminal.json').read_text())
 assert rec['exit']==0 and rec['reason'] is None and rec['pins']==rec['after'] and rec['direct_imports']==rec['direct_imports_after']
 assert sha(s)==sha(o/'source.txt')==rec['pins']['source'] and sha(run)==rec['pins']['runner']
 assert not re.search(r'\b(?:sorry|admit)\b',s.read_text())
 assert sha(o/'stdout')==rec['stdout_sha256'] and sha(o/'stderr')==rec['stderr_sha256']
 assert sha(Path(rec['output_root'])/(name+'.olean'))==rec['object_sha256']==output
 logs=(o/'stdout').read_text()+(o/'stderr').read_text()
 for th in theorems:assert f"'{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in logs
 assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
 imports=[m for line in s.read_text().splitlines() if line.startswith('import ') for m in line[7:].split()]
 assert imports==[x['module'] for x in rec['direct_imports']]
 print(name,'source',sha(s),'runner',sha(run),'object',output,'terminal',sha(o/'terminal.json'))
 for imp in rec['direct_imports']:
  sel=next(Path(x)/(imp['module'].replace('.','/')+'.olean') for x in rec['lean_path'].split(':') if (Path(x)/(imp['module'].replace('.','/')+'.olean')).is_file())
  assert str(sel.resolve())==imp['path'] and sha(sel)==imp['sha256'] and sha(sel) in rec['pins']['extra']
  assert imp['sha256'] in run.read_text()
  print(' ',imp['module'],imp['path'],imp['sha256'])
print('PASS: receipt and current first-direct-selection checks; no Lean replay')
