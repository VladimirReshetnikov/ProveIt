import hashlib, json, pathlib, subprocess, sys
root = pathlib.Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
r = root / 'Computability/DiophantineConsistency/research'
base = r / 'nine-sharing-norm38-reference-fields01-check'
old = {'manifest':'f5730ba00ce4e9e811a8e8d202658c224e7e22d4582584090921b44d8a3fde8c','survey':'f6944be120881878542dc669a7ecc9e8fcda8b6fb7ebd508d6f0faca43fdb48e'}
data = {'02': {'source':'d4b1bccc444a1e87e10cc2ab95c356e304be2b9666244a6d1322deab2aadef54','manifest':'90475b11486c3b3231c76cabc4bd475f66325695d04076857cd235b6b574097d','survey':'e4a12b10b3c650a44fde4801d781834b08a10728daf0d2976b03d739d66be965','runner':'879bf960105fe38d61d4f74aaf4210a745b94bc2d264fbd06a5f58bf50acf2ac','fields':[('U',78),('W',66)]},'03': {'source':'7fcd23b2c5d32ead949e1a2e640c59041bcd8a6a948a8c7bf45497b342beb153','manifest':'1a774e1d88ae70778b7626ef94c51d3e48a8aca513a835003a60aea2b70b9c05','survey':'0752650941498baf2d0270fdadb6edc60ae0a0058abcd5c5b0236de40fc1df91','runner':'fd181963ef0a76645ec06569e8f805061a0639a334be1f154daf85e6192ff4fb','fields':[('Z',80),('delta',36)]}}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert digest(base/'source-manifest.json') == old['manifest']
assert digest(base/'carrier_preflight.py') == old['survey']
for n,d in data.items():
 p = r / ('nine-sharing-norm38-reference-fields'+n+'-check')
 files = {'source': p/'src/DiophantineConsistency'/('Norm38ReferenceFields'+n+'.lean'), 'manifest': p/'source-manifest.json', 'survey':p/'carrier_preflight.py', 'runner':p/'run.py'}
 for k,f in files.items(): assert digest(f) == d[k], (n,k)
 oldrun=(base/'run.py').read_text(); expected=oldrun.replace('reference-fields01-check-20261105','reference-fields'+n+'-check-20261105').replace(old['manifest'],d['manifest']).replace(old['survey'],d['survey'])
 assert files['runner'].read_text()==expected, ('runner delta',n)
 assert files['survey'].read_text()==(base/'carrier_preflight.py').read_text().replace('Norm38ReferenceFields01.olean','Norm38ReferenceFields'+n+'.olean'), ('survey delta',n)
 source=files['source'].read_text()
 assert source.count('\ntheorem ')==2 and 'sorry' not in source
 for field, idx in d['fields']:
  statement=f'theorem reference_{field} {{R : Type*}} [CommRing R] (p : Fin 4 → R) (x : Fin 14 → R) :\n    reference p x {idx} = (Carrier65.core p x).{field} := by\n  simp [reference, Carrier65.core] <;> ring'
  assert statement in source, (n,field)
  assert f'#print axioms DiophantineConsistency.Norm38Reference.reference_{field}' in source
 manifest=json.loads(files['manifest'].read_text())['rows']; assert len(manifest)==1
 row=manifest[0]; assert row['source_sha256']==d['source'] and root.joinpath(row['source'])==files['source']
 assert row['module']=='DiophantineConsistency.Norm38ReferenceFields'+n
 assert row['imports']==['DiophantineConsistency.Norm38ReferenceBase','DiophantineConsistency.Carrier65']
 result=subprocess.run([sys.executable,'-I','-S','-B',str(files['runner']),'--preflight'],cwd=root,text=True,capture_output=True,timeout=90)
 assert result.returncode==0 and 'PASS_NO_LEAN_PREFLIGHT' in result.stdout, (n,result.returncode,result.stdout,result.stderr)
 print(n, 'PASS: pinned sources, exact runner/survey deltas, four projection statements, no-Lean preflight')
print('PASS; no Lean replay or theorem success asserted')
