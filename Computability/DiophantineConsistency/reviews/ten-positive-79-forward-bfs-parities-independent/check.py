#!/usr/bin/env python3
"""Independent read-only receipt and selected direct-import check; no Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2]
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b: raise RuntimeError(m)
def scan(d,source,runner,attempt,obj,reports):
 p=D/'research'/d;o=p/'observations'/attempt;s=p/source;t=json.loads((o/'terminal.json').read_text());r=pathlib.Path(t['output_root']);pins=t['pins']
 need(t['exit']==0 and t['reason'] is None and pins==t['after'],'exit or pins')
 need(sha(s)==pins['source']==sha(o/'source.txt')==sha(r/source),'source')
 need(sha(p/runner)==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner or Lean')
 need(sha(r/(s.stem+'.olean'))==t['object_sha256']==obj,'object')
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'log hashes')
 need((o/'stdout').read_text()==''.join(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in reports) and (o/'stderr').read_text()=='','reports')
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)
 records=pins.get('direct_imports',t.get('direct_imports'))
 if isinstance(records,dict):records=[dict(module=k,**v) for k,v in records.items()]
 if 'direct_imports_after' in t:need(t['direct_imports']==t['direct_imports_after'],'snapshots')
 need({x['module'] for x in records}==set(imports) and len(records)==len(imports),'import coverage')
 direct=[]
 for x in records:
  rel=x['module'].replace('.','/')+'.olean'
  found=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
  need(found and found.resolve()==pathlib.Path(x['path']).resolve() and sha(found)==x['sha256'],'resolution '+x['module'])
  direct.append({'module':x['module'],'path':str(found.resolve()),'sha256':sha(found)})
 for x in t.get('stage_receipts',[]):need(sha(x['path'])==x['sha256'],'stage receipt')
 return {'source_sha256':sha(s),'runner_sha256':sha(p/runner),'object_sha256':obj,'imports':direct,'stage_receipts':len(t.get('stage_receipts',[]))}
a=scan('ten-positive-79-guarded-model-probe','Mask79Forward.lean','run-forward.py','forward-attempt02','3469bbdc3d8c50c22b06dd5a5ce01bd8f72c2aa392f9cadb0fd8b3f5080fdd0a',['TenPositive79Forward.positive_zero_iff_guarded'])
b=scan('direct-bfs-word-field-parity-prototype','DirectBFSWordFieldParity.lean','run.py','directbfswordfieldparity-attempt02','123125d4ecaf64734fe9cdc8052c5903fb5190eeb5adcabd21f38c9682680de9',['DirectBFSWordFieldParity.word_low_slots','DirectBFSWordFieldParity.vertical_even','DirectBFSWordFieldParity.horizontal_even'])
c=scan('direct-bfs-word-marker-parity-prototype','DirectBFSWordMarkerParity.lean','run.py','directbfswordmarkerparity-attempt01','94324f83cc263ce659bc249bea93de93c043e3d555625856c88aa1fd755d46a3',['DirectBFSWordMarkerParity.marker_digit','DirectBFSWordMarkerParity.vertical_marker_even','DirectBFSWordMarkerParity.horizontal_marker_even'])
need(next(x for x in a['imports'] if x['module']=='Mask79Guarded')['sha256']=='3bba5208ea586c4451aaeb3b4e4056bd81db5489ca9d3ac32ac100c8b03358c0','guarded provider')
need(next(x for x in b['imports'] if x['module']=='DirectBFSWordFieldCyclic')['sha256']=='6b14bb325f225d7480f5ec14926debb6b8ae0a72a3842bb05baa444b0c24d449','cyclic provider')
need(next(x for x in c['imports'] if x['module']=='DirectBFSWordFieldParity')['sha256']==b['object_sha256'],'field provider')
print(json.dumps({'status':'PASS','forward':a,'field':b,'marker':c,'lean_replayed':False},indent=2,sort_keys=True))
