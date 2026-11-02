#!/usr/bin/env python3
"""Point-in-time three-source aligned two-band closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];RESEARCH=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';REVIEW=ROOT/'Computability/DiophantineConsistency/reviews/compact44-partial-band-rotation-closure-independent-audit';BASE=RESEARCH/'compact44-partial-band-rotation-closure-plan';SOURCE=RESEARCH/'compact44-two-band-rotation-prototype/TwoBand.lean';PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01')
PINS={REVIEW/'audit.py':'142e250c0828b41f8dbe21d9bf787799781465470990950ac58cfa28acddae57',REVIEW/'CHECK.json':'b623a2d6e51d57fdb5838466cb70bcf18a7fa090c0851ad7a08697d466cecde8',REVIEW/'terminal-observation.json':'0c5672441330811db78e062c3332afb28fd5f85e28049fe9255e08741dca3531',BASE/'scan.py':'b623cc0de936c658fc6835556d7fbd585160d1a2ff1dc399e2514eb12bffb2e5',BASE/'scan.json':'0bc9f86e40d08f2d40d27b84c1cc6b4b703082b61c45003b61469decd6fbe7ae',BASE/'terminal-observation.json':'f557656e581bf2a13a33aecd282fe82a96d43225b714261fb78a6b43d66f92bf',SOURCE:'6bf2dc0cf02bc32ccff07cc5cc3b66f271fc86bed01dfc151a07f39893a48908'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():assert p.is_file() and H(p)==h,('pin',str(p))
base=json.loads((BASE/'scan.json').read_bytes());review=json.loads((REVIEW/'CHECK.json').read_bytes());obs=json.loads((REVIEW/'terminal-observation.json').read_bytes());assert base['status']=='PRELIMINARY_PARTIAL_BAND_ROTATION_SOURCE_CLOSURE_NOT_A_BUILD' and base['objects_per_side']==126 and len(base['external_direct_slots'])==40 and len(base['first_target_slots'])==20 and len(base['second_target_slots'])==20 and len(base['init_slots'])==10
assert review['status']=='PASS_INDEPENDENT_PARTIAL_BAND_ROTATION_SOURCE_CLOSURE' and review['reviewed_commit']=='0d23719613' and review['objects_per_side']==126 and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['lean_launched'] is False and obs['check_sha256']==PINS[REVIEW/'CHECK.json']
q=subprocess.run([sys.executable,'-I','-S','-B',str(BASE/'scan.py')],cwd=ROOT,capture_output=True,timeout=2400);assert q.returncode==0 and not q.stderr and q.stdout==(BASE/'scan.json').read_bytes(),('base scan',q.returncode,q.stderr)
q=subprocess.run([sys.executable,'-I','-S','-B',str(REVIEW/'audit.py')],cwd=ROOT,capture_output=True,timeout=2400);assert q.returncode==0 and not q.stderr and json.loads(q.stdout)==review,('base audit',q.returncode,q.stderr)
blob=subprocess.run(['git','show','d71872eb82:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==PINS[SOURCE]
imports=[line[7:] for line in SOURCE.read_text().splitlines() if line.startswith('import ')];assert imports==['DiophantineConsistency.CompactPartialBandRotation']
reports=re.findall(r'^#print axioms\s+(\S+)',SOURCE.read_text(),re.M);assert reports==['TwoBand.bare_congr','TwoBand.add_congr_mod','TwoBand.combined_congr']
targets={}
for side in ('author','peer'):
 stem=PARENT/side/'lib/DiophantineConsistency/TwoBand'
 for suf in SUFFIXES:
  p=Path(str(stem)+suf);assert not os.path.lexists(p),str(p);targets[str(p)]=None
assert len(targets)==20
for p,h in PINS.items():assert H(p)==h,('pin after review',str(p))
print(json.dumps({'status':'PRELIMINARY_TWO_BAND_ROTATION_SOURCE_CLOSURE_NOT_A_BUILD','source_order':[base['first_source'],base['second_source'],{'module':'DiophantineConsistency.TwoBand','source':str(SOURCE),'source_commit':'d71872eb82','sha256':PINS[SOURCE],'imports':imports,'reports':reports}],'base_scan_sha256':PINS[BASE/'scan.json'],'base_review_sha256':PINS[REVIEW/'CHECK.json'],'objects_per_side':126,'external_direct_slots':base['external_direct_slots'],'first_target_slots':base['first_target_slots'],'second_target_slots':base['second_target_slots'],'third_target_slots':targets,'init_slots':base['init_slots'],'scope':'Point-in-time three-source closure; hK and graph congruence are assumptions, and no fractional alignment, retained-byte, full column, machine or iPRA theorem follows.'},indent=2,sort_keys=True))
