#!/usr/bin/env python3
"""Independent batched source/runner comparison; no Lean invocation."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-slots-batched-draft';prior=D/'research/nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean';seed=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(prior)=='7afacc8c1f2b9b0e1b443f346653c21dde511fe200e8296daf2ec2afd4ea38fc' and sha(seed)=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23'
assert sha(q/'source-manifest.json')=='97c061c885b7be6495b1244713b31fea1ff0ac955b493e066eaa1139c8ab40ac' and sha(q/'run.py')=='88663c80c9a55fe3b8b1411aec5990a19c44734202f9bdbf624e5530fa96c938'
assert sha(q/'generate.py')=='c371af0a3a30cfc3c7399704516bc2c3bd823a951998a096178adca5449717be'
data=json.loads(seed.read_text());up=prior.read_text();oldrunner=(D/'research/nine-sharing-norm38-slot-extraction-check/run.py').read_text();run=(q/'run.py').read_text()
for a,b in [('/tmp/nine-sharing-norm38-slot-check-20261105','/tmp/nine-sharing-norm38-slots-batched-20261105'),('4936a8eaa5b3b0fdc03f825dcbdf5fb6621e4dff8d88f7547d441dde8238d32f','97c061c885b7be6495b1244713b31fea1ff0ac955b493e066eaa1139c8ab40ac'),('single-module unverified norm38 slot-extraction experiment','twelve-module batched norm38 slot experiment'),('PASS norm38 slot-extraction check','PASS batched norm38 slot check')]:assert a in oldrunner;oldrunner=oldrunner.replace(a,b)
assert oldrunner==run
manifest=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(manifest)==12
names=['Norm38SlotsBase']+[f'Norm38Slots{i:02d}' for i in range(10)]+['Norm38SlotsAssembly'];assert [r['module'].split('.')[-1] for r in manifest]==names
base=json.loads((D/'research/nine-sharing-seed38-weighted-retry/attempt01/state.json').read_text());basepath=Path('/tmp/nine-sharing-seed38-weighted-retry-20261105/lib');seen=set()
for row in manifest:
 n=row['module'].split('.')[-1];source=q/'src/DiophantineConsistency'/(n+'.lean');assert sha(source)==row['source_sha256'];imports=re.findall(r'^import ([A-Za-z0-9_.]+)$',source.read_text(),re.M);assert imports==row['imports']
 assert all(dep in seen for dep in imports if dep in {x['module'] for x in manifest});seen.add(row['module']);assert str(basepath/'DiophantineConsistency'/(n+'.olean')) not in base['overlay_links'] and all(x['module']!=n for x in base['rows'])
def variables(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 return variables(t[1])|variables(t[2])
for i,r in enumerate(data['residuals']):
 source=(q/'src/DiophantineConsistency'/f'Norm38Slots{i//3:02d}.lean').read_text();name=f'slot{i:02d}'
 stmt=lambda s:re.search(r'^theorem '+name+r'\b.*? := by',s,re.S|re.M).group()
 assert stmt(source)==stmt(up)
 body=re.search(r'^theorem '+name+r'\b.*?(?=^/-- Slot \d+:|^end )',source,re.M|re.S).group()
 ids=variables(r['expr']);assert 0 not in ids and set(map(int,re.findall(r'^  have h(\d\d) :',body,re.M)))==ids
 for n in ids:
  assert f'(Fin.cons (1 : V) w : Fin 39 → V) {n} = w {n-1}' in body
  assert f'({n-1} : Fin 38).succ = ({n} : Fin 39)' in body
  assert f'Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w ({n-1} : Fin 38)' in body
assert sum(len(re.findall(r'^theorem slot\d\d\b',(q/'src/DiophantineConsistency'/f'Norm38Slots{i:02d}.lean').read_text(),re.M)) for i in range(10))==29
assembly=(q/'src/DiophantineConsistency/Norm38SlotsAssembly.lean').read_text();part=lambda s:s[s.index('/-- The sum-of-squares theorem'):s.rindex('end DiophantineConsistency.Norm38SlotExtraction')].strip();assert part(assembly)==part(up)
assert all('import DiophantineConsistency.Norm38Slots'+f'{i:02d}' in assembly for i in range(10))
print(json.dumps({'status':'PASS_SOURCE_RUNNER_REVIEW_ONLY','runner_sha256':sha(q/'run.py'),'manifest_sha256':sha(q/'source-manifest.json'),'stages':12,'slots':29,'scope':'Statement text/index/runner comparison only; no Lean, proof, model bridge or endpoint.'},indent=2,sort_keys=True))
