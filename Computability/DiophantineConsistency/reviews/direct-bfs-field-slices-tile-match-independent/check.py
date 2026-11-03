#!/usr/bin/env python3
"""Inspect frozen author receipts and current direct object selection; no Lean replay."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2]; R=D/'research'
rows=[('direct-bfs-lean-field-slices-prototype','DirectBFSFieldSlices','directbfsfieldslices-attempt01',['DirectBFSDecodedPayloadBits.bit','DirectBFSVerticalFieldBits.fields','DirectBFSVerticalFieldBits.positions','DirectBFSVerticalFieldBits.bit','DirectBFSHorizontalFieldBits.previous','DirectBFSHorizontalFieldBits.fields'],'a05523b42e4f25203d88f1ab2aa3a2a1fe966fc0927633d47b9ab4c14bf97079'),('direct-bfs-80-tile-match-prototype','DirectBFS80TileMatch','directbfs80tilematch-attempt01',['DirectBFS80TileMatch.graph_tile_match'],'fdbb44ab0a96a8b835f168be5a261cefe05e1dc3a2b79ac6563969c25d732ed5')]
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
for dirname,name,attempt,theorems,output in rows:
 p=R/dirname;s=p/(name+'.lean');run=p/'run.py';o=p/'observations'/attempt;rec=json.loads((o/'terminal.json').read_text())
 assert rec['exit']==0 and rec['reason'] is None and rec['pins']==rec['after'] and rec['direct_imports']==rec['direct_imports_after']
 assert sha(s)==sha(o/'source.txt')==rec['pins']['source'] and sha(run)==rec['pins']['runner']
 assert sha(o/'stdout')==rec['stdout_sha256'] and sha(o/'stderr')==rec['stderr_sha256']
 assert sha(Path(rec['output_root'])/(name+'.olean'))==rec['object_sha256']==output
 logs=(o/'stdout').read_text()+(o/'stderr').read_text()
 for th in theorems:
  ax="[propext, Quot.sound]" if th.endswith(".positions") else "[propext, Classical.choice, Quot.sound]"
  assert f"'{th}' depends on axioms: {ax}" in logs
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
