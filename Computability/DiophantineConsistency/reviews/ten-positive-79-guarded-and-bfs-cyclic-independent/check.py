#!/usr/bin/env python3
"""Read-only receipt and first import audit, without Lean replay."""
import hashlib, json, pathlib, re
D=pathlib.Path(__file__).resolve().parents[2]
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b: raise ValueError(m)
def scan(directory, source, attempt, expected_obj, reports, names):
 p=D/'research'/directory; o=p/'observations'/attempt
 s=p/source;t=json.loads((o/'terminal.json').read_text()); root=pathlib.Path(t['output_root']); pins=t['pins']
 need(t['exit']==0 and t['reason'] is None and pins==t['after'],'exit or before/after pins')
 need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/source),'source')
 need(sha(p/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner or lean')
 need(sha(root/(s.stem+'.olean'))==t['object_sha256']==expected_obj,'object')
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'log hashes')
 need((o/'stdout').read_text()==''.join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for name in reports) and (o/'stderr').read_text()=='','diagnostic reports')
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'source placeholder')
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M)
 need(imports==names,'direct import list')
 records=pins.get('direct_imports',t.get('direct_imports'))
 if isinstance(records,dict): records=[dict(module=k,**v) for k,v in records.items()]
 if 'direct_imports_after' in t: need(t['direct_imports']==t['direct_imports_after'],'direct snapshots')
 need({x['module'] for x in records}==set(imports),'direct coverage')
 selected=[]
 for record in records:
  m=record['module']; rel=m.replace('.','/')+'.olean'
  path=next((pathlib.Path(d)/rel for d in t['lean_path'].split(':') if (pathlib.Path(d)/rel).is_file()),None)
  need(path is not None and path.resolve()==pathlib.Path(record['path']).resolve() and sha(path)==record['sha256'],'selection '+m)
  selected.append({'module':m,'path':str(path.resolve()),'sha256':sha(path)})
 return {'source_sha256':sha(s),'runner_sha256':sha(p/'run.py'),'object_sha256':expected_obj,'imports':selected}
g=scan('ten-positive-79-guarded-model-probe','Mask79Guarded.lean','guarded-attempt03','3bba5208ea586c4451aaeb3b4e4056bd81db5489ca9d3ac32ac100c8b03358c0',['TenPositive79Guarded.guarded_to_old'],['MaskCoordinate79','Direct80TransportModel'])
b=scan('direct-bfs-word-field-cyclic-prototype','DirectBFSWordFieldCyclic.lean','directbfswordfieldcyclic-attempt03','6b14bb325f225d7480f5ec14926debb6b8ae0a72a3842bb05baa444b0c24d449',['DirectBFSWordColorBits.vertical_bits','DirectBFSWordColorBits.horizontal_bits','DirectBFSWordFieldDigits.vertical_digits','DirectBFSWordFieldDigits.horizontal_digits','DirectBFSWordFieldCyclic.vertical_sources','DirectBFSWordFieldCyclic.horizontal_sources'],['DirectBFSHighOnlyPacking','DirectBFSTileFields','DiophantineConsistency.HorizontalFieldBits'])
need(next(x for x in g['imports'] if x['module']=='MaskCoordinate79')['sha256']=='7fac254b7efc456af7f4aa03ac2d1fa80c23c18faac88ccfd46914b3d07184f6','79 ring provider')
print(json.dumps({'status':'PASS','guarded':g,'bfs_cyclic':b,'lean_replayed':False},indent=2,sort_keys=True))
