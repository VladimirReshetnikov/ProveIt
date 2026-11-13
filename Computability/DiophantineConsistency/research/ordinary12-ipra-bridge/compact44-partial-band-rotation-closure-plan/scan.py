#!/usr/bin/env python3
"""Point-in-time two-source partial-band closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];RESEARCH=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';REVIEW=ROOT/'Computability/DiophantineConsistency/reviews/compact44-partial-band-closure-independent-audit';BASE=RESEARCH/'compact44-partial-band-closure-plan';SOURCE=RESEARCH/'compact44-partial-band-rotation-prototype/CompactPartialBandRotation.lean';PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01')
PINS={REVIEW/'audit.py':'c58f556fceb5c81c52ddb16419d4532f3496584801b468eb7372f1d2a5922b15',REVIEW/'CHECK.json':'1950866b6ca64631c9837fce924f0e8663c345525945f9364b304454686be667',REVIEW/'terminal-observation.json':'8d8b5568d36c9b41769ed95deabed863502369739cbac8c208a018f50d3de288',BASE/'scan.py':'2e839fe0350645a0348958d18b279218b6464c9ec151b0c0a1e279ff65082801',BASE/'scan.json':'448e3d7be056a54908a0d79f5b5e1dce186d209b96fa752b28414cc1f3abde0d',BASE/'terminal-observation.json':'a203f6e6d86eeddc86fd8026855f6b8927086e02195d3a0c6e1fd9839cf3645e',SOURCE:'a74f981ea103fabce4163336233071018bbba7a445db05a67ee7207af8cc1438'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():assert p.is_file() and H(p)==h,('pin',str(p))
base=json.loads((BASE/'scan.json').read_bytes());review=json.loads((REVIEW/'CHECK.json').read_bytes());obs=json.loads((REVIEW/'terminal-observation.json').read_bytes());assert base['status']=='PRELIMINARY_PARTIAL_BAND_SOURCE_CLOSURE_NOT_A_BUILD' and len(base['objects'])==126 and len(base['direct_slots'])==40 and len(base['target_slots'])==20 and len(base['init_slots'])==10
assert review['status']=='PASS_INDEPENDENT_PARTIAL_BAND_SOURCE_CLOSURE' and review['plan_commit']=='7ae590be72' and review['provider_objects_per_side']==126 and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['lean_launched'] is False and obs['check_sha256']==PINS[REVIEW/'CHECK.json']
q=subprocess.run([sys.executable,'-I','-S','-B',str(BASE/'scan.py')],cwd=ROOT,capture_output=True,timeout=180);assert q.returncode==0 and not q.stderr and q.stdout==(BASE/'scan.json').read_bytes(),('base scan',q.returncode,q.stderr)
q=subprocess.run([sys.executable,'-I','-S','-B',str(REVIEW/'audit.py')],cwd=ROOT,capture_output=True,timeout=1800);assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==review,('base audit',q.returncode,q.stderr)
blob=subprocess.run(['git','show','6fde7b8487:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==PINS[SOURCE]
imports=[line[7:] for line in SOURCE.read_text().splitlines() if line.startswith('import ')];assert imports==['DiophantineConsistency.CompactPartialBand']
reports=re.findall(r'^#print axioms\s+(\S+)',SOURCE.read_text(),re.M);assert reports==['CompactPartialBandRotation.band_rotation_congr','CompactPartialBandRotation.band_column']
targets={}
for side in ('author','peer'):
 stem=PARENT/side/'lib/DiophantineConsistency/CompactPartialBandRotation'
 for suf in SUFFIXES:
  p=Path(str(stem)+suf);assert not os.path.lexists(p),str(p);targets[str(p)]=None
assert len(targets)==20
for p,h in PINS.items():assert H(p)==h,('pin after review',str(p))
print(json.dumps({'status':'PRELIMINARY_PARTIAL_BAND_ROTATION_SOURCE_CLOSURE_NOT_A_BUILD','first_source':{'module':'DiophantineConsistency.CompactPartialBand','source':base['source'],'sha256':base['source_sha256'],'imports':base['imports'],'reports':base['axiom_reports']},'second_source':{'module':'DiophantineConsistency.CompactPartialBandRotation','source':str(SOURCE),'source_commit':'6fde7b8487','sha256':PINS[SOURCE],'imports':imports,'reports':reports},'base_scan_sha256':PINS[BASE/'scan.json'],'base_review_sha256':PINS[REVIEW/'CHECK.json'],'objects_per_side':126,'external_direct_slots':base['direct_slots'],'first_target_slots':base['target_slots'],'second_target_slots':targets,'init_slots':base['init_slots'],'scope':'Point-in-time two-source closure with base source review rerun; no paired build, full graph-column, fractional temporal alignment, retained byte binding, machine or iPRA proof.'},indent=2,sort_keys=True))
