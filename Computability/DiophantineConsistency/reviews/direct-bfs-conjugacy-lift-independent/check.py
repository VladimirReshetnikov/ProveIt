#!/usr/bin/env python3
"""Review accepted lift receipt and provider chain, without invoking Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-lean-conjugacy-lift-prototype';S=P/'DirectBFSConjugacyLift.lean';run=P/'run-v2.py';obs=P/'observations/directbfsconjugacylift-attempt02';old=P/'observations/directbfsconjugacylift-attempt01'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
def j(x):return json.loads(Path(x).read_text())
t=j(obs/'terminal.json');failed=j(old/'terminal.json');assert t['exit']==0 and t['reason'] is None and t['pins']==t['after'] and t['direct_imports']==t['direct_imports_after']
assert sha(S)==sha(obs/'source.txt')==t['pins']['source']=='fa709d15826bf52ca2d8da275cedf97912ead112ef2a7afa6643e717028c6761'
assert sha(run)==t['pins']['runner']=='d408c08a72e1cdc37537869a2c1d7497e06a4c0ecb56f0b6726289a8451909b5'
assert not re.search(r'\b(?:sorry|admit)\b',S.read_text())
assert sha(obs/'stdout')==t['stdout_sha256'] and sha(obs/'stderr')==t['stderr_sha256']
obj=Path(t['output_root'])/'DirectBFSConjugacyLift.olean';assert sha(obj)==t['object_sha256']=='4ff48994bfef89bf7bce5e1473a261dd7eb19e07fd579cd7658dede08716c39e'
logs=(obs/'stdout').read_text()+(obs/'stderr').read_text();assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
names=['row_bijective','horizontal_bijective','vertical_bijective','row_match_fin','row_match','row_inverse','row_bounds','horizontal_inverse','horizontal_bounds','vertical_inverse','vertical_bounds']
for name in names:
 ax='[propext, Classical.choice, Quot.sound]' if name.endswith('_bijective') else '[propext, Quot.sound]'
 assert logs.count(f"'DirectBFSConjugacyLift.{name}' depends on axioms: {ax}")==1
imports=re.findall(r'^import\s+(\S+)$',S.read_text(),re.M);assert imports==[x['module'] for x in t['direct_imports']] and len(imports)==2
print('source',sha(S),'runner',sha(run),'object',sha(obj),'terminal',sha(obs/'terminal.json'))
for x in t['direct_imports']:
 selected=next(Path(d)/(x['module'].replace('.','/')+'.olean') for d in t['lean_path'].split(':') if (Path(d)/(x['module'].replace('.','/')+'.olean')).is_file())
 assert str(selected.resolve())==x['path'] and sha(selected)==x['sha256'] and sha(selected) in t['pins']['extra']
 print(x['module'],x['path'],x['sha256'])
assert len(t['stage_receipts'])==59
for it in t['stage_receipts']:assert sha(it['path'])==it['sha256']
assert failed['exit']!=0 and sha(old/'stdout')==failed['stdout_sha256'] and sha(old/'stderr')==failed['stderr_sha256']
assert 'maximum recursion depth' in (old/'stdout').read_text() and 'sorryAx' in (old/'stdout').read_text()
assert (old/'source.txt').read_text().replace('set_option Elab.async false\n','set_option Elab.async false\nset_option maxRecDepth 16384\n',1)==S.read_text()
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/direct-bfs-conjugacy-aggregate-accepted-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS 11 axiom reports, 2 direct providers, 59 receipts, aggregate output chain; failed attempt and source diff verified; no Lean replay')
