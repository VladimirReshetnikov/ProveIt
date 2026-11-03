#!/usr/bin/env python3
"""Check retained sources, receipts and provider selections; do not invoke Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2]
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
cases=[('direct-bfs-active-phase-packing-prototype','DirectBFSActivePhasePacking','directbfsactivepack-attempt02','f857acb162ea08b5c28cf48fd1cc6d0a4263472e333ae5e732cb9233fd092630'),('direct-bfs-word-field-high-prototype','DirectBFSWordFieldHigh','directbfswordfieldhigh-attempt01','c3776f135922c9f6653515d59bf02113358e38cd97804f1c2b2ad764e3aee1ca'),('direct-bfs-word-anchor-high-prototype','DirectBFSWordAnchorHigh','directbfswordanchorhigh-attempt01','ee334988dbe381bf8706e15907be36e2e472416b703399af23e171c2ed4fd3e5'),('direct-bfs-marked-target-prototype','DirectBFSMarkedTarget','directbfsmarkedtarget-attempt01','15c2bba9cac700db12a6a1536fb6391463f806d10be40e539e6d465d13e862c0'),('direct-bfs-word-packing-prototype','DirectBFSWordPacking','directbfswordpacking-attempt02','c1ad37e318c176a0ae9b46e3b0be74b5bcc813ae120a3636d282aaeba5726d86')]
allresults={}
for folder,mod,attempt,obj in cases:
 p=D/'research'/folder;s=p/(mod+'.lean');o=p/'observations'/attempt;t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
 need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],mod+' state')
 need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),mod+' source')
 runner=p/('run-v2.py' if mod=='DirectBFSActivePhasePacking' else 'run.py')
 need(sha(runner)==pins['runner'] and sha(t['command'][0])==pins['lean'],mod+' runner')
 need(sha(root/(mod+'.olean'))==t['object_sha256']==obj,mod+' object')
 need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],mod+' logs')
 reports=re.findall(r'^#print axioms ([\w.]+)$',s.read_text(),re.M)
 need((o/'stdout').read_text()==''.join(f"'{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in reports) and (o/'stderr').read_text()=='',mod+' reports')
 need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),mod+' placeholder')
 imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);records=t['direct_imports']
 need([x['module'] for x in records]==imports,mod+' direct imports')
 for x in records:
  rel=x['module'].replace('.','/')+'.olean';first=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
  need(first and first.resolve()==pathlib.Path(x['path']).resolve() and sha(first)==x['sha256'],mod+' resolution '+x['module'])
 for x in t.get('stage_receipts',[]):need(sha(x['path'])==x['sha256'],mod+' chunk receipt')
 allresults[mod]={'object_sha256':obj,'source_sha256':sha(s),'runner_sha256':sha(runner),'reports':reports,'imports':records,'stage_receipts':len(t.get('stage_receipts',[]))}
for mod in ('DirectBFSActivePhasePacking','DirectBFSWordFieldHigh','DirectBFSMarkedTarget'):
 need(next(x for x in allresults['DirectBFSWordPacking']['imports'] if x['module']==mod)['sha256']==allresults[mod]['object_sha256'],'packing '+mod)
need(next(x for x in allresults['DirectBFSMarkedTarget']['imports'] if x['module']=='DirectBFSWordAnchorHigh')['sha256']==allresults['DirectBFSWordAnchorHigh']['object_sha256'],'target anchor')
packing_receipt=D/'research/direct-bfs-word-packing-prototype/observations/directbfswordpacking-attempt02/terminal.json'
roots=json.loads(packing_receipt.read_text())['lean_path'].split(':')
for module,want in {'DirectBFSWordAnchorHigh':allresults['DirectBFSWordAnchorHigh']['object_sha256'],'DirectBFSWordMarkerParity':'94324f83cc263ce659bc249bea93de93c043e3d555625856c88aa1fd755d46a3','DirectBFSWordFieldParity':'123125d4ecaf64734fe9cdc8052c5903fb5190eeb5adcabd21f38c9682680de9','DirectBFSHighPadding':'8bcae890b9601d0087572a4e73ef8b3e7ed0a9e190f147f23a6502b5b6402617','DirectBFSFourFieldsPacking':'cfd3cc0045adbca24395a947ac2a4855ac94b313318f9c81660e38818ee3601c'}.items():
 path=next((pathlib.Path(x)/(module+'.olean') for x in roots if (pathlib.Path(x)/(module+'.olean')).is_file()),None)
 need(path and sha(path)==want,'packing inherited selection '+module)
 allresults['DirectBFSWordPacking'].setdefault('selected_ancestors',[]).append({'module':module,'path':str(path),'sha256':want})
print(json.dumps({'status':'PASS','packets':allresults,'lean_replayed':False},indent=2,sort_keys=True))
