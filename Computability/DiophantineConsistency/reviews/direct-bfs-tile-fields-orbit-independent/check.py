#!/usr/bin/env python3
"""Inspect frozen author receipts and current direct object selection; no Lean replay."""
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2]; R=D/'research'
rows=[('direct-bfs-lean-tile-fields-prototype','DirectBFSTileFields','directbfstilefields-attempt01',['DirectBFSTileFields.tile_fields'],'68fef4ae214e8a9992ef32b9f476da016bc99e73941d9b36bf86f019cd5ede66'),('direct-bfs-lean-block-orbit-prototype','DirectBFSBlockOrbit','directbfsblockorbit-attempt02',['DirectBFSBlockOrbit.decoded_occupied','DirectBFSBlockOrbit.selected_iff_digit','DirectBFSBlockOrbit.occupied_successor','DirectBFSBlockOrbit.orbit_all'],'0faaa0cef80907550b5dcdcf0ac9168c351c6c1d3473f35e0875d90b3c65453b')]
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
for dirname,name,attempt,theorems,output in rows:
 p=R/dirname;s=p/(name+'.lean');run=p/'run.py';o=p/'observations'/attempt;rec=json.loads((o/'terminal.json').read_text())
 assert rec['exit']==0 and rec['reason'] is None and rec['pins']==rec['after'] and rec['direct_imports']==rec['direct_imports_after']
 assert sha(s)==sha(o/'source.txt')==rec['pins']['source'] and sha(run)==rec['pins']['runner']
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
