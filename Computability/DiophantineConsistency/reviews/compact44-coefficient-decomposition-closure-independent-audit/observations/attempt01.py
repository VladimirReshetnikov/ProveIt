#!/usr/bin/env python3
"""Independent point-in-time same-side decoder/coefficient closure review."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
BASE=Path(__file__).resolve().parents[2];ROOT=BASE.parents[1];R=BASE/'research/ordinary12-ipra-bridge';PLAN=R/'compact44-coefficient-decomposition-closure-plan';SOURCE=R/'compact44-coefficient-decomposition-prototype/CompactCoefficientDecoder.lean';REV=BASE/'reviews'
DEC=Path('/tmp/ipra-compact943-decoder-pair-01');MASS=Path('/tmp/ipra-compact-coefficient-mass-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={PLAN/'README.md':'fa693afe9bca2a8ae146ab74eeea00d99696cba0f9bcec7f8dd85e115d2a331e',PLAN/'scan.py':'853c7bf77369c1231cfa79349b107c547056725515959c2f09870bf6a3a3c2c8',PLAN/'scan.json':'3fab03590ed1723c04213c2a916d2c9476f51e9c1384ea73310883e1f486e6f4',PLAN/'terminal-observation.json':'9ac7188fdc452a1bd5cd890e8fdf0c416d9700ed2883cbfd8fa51720b4f20e79',SOURCE:'86f9ddd083eb5767359a691774c76c88a5e7c1627dc693f474880a78e32a03c8'}
AUDITS=[(REV/'compact44-943-decoder-independent-audit','5a6695bd9fe61ae0d04331170eef880aa0bbea185b5dc3227950fc812877d578','5a29da0ea330d1781372fd5d2c8fd22c36a87eaa215b315720c087400d3618d3','PASS_INDEPENDENT_COMPACT_943_DECODER_AUDIT'),(REV/'compact44-coefficient-mass-independent-audit','9fc48750f7846e6f2b5cfe3ea93b14935720fd04115b45e8cbf276b02af92a55','86e0753623b1f8d7ce2e0c0134e02e84430eccf53174d580f0de477e836b87e7','PASS_INDEPENDENT_COMPACT44_COEFFICIENT_MASS_AUDIT')]
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def slots(stem):
 out={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):need(p.is_file(),'invalid slot '+str(p));out[suffix]={'sha256':H(p),'realpath':str(p.resolve())}
  else:out[suffix]=None
 return out
for p,h in PINS.items():need(H(p)==h,'pin '+str(p))
obs=json.loads((PLAN/'terminal-observation.json').read_bytes());need(obs['observed_exit']==0 and obs['optimized_exit']==1 and obs['lean_launched'] is False and obs['scan_sha256']==PINS[PLAN/'scan.json'] and obs['scanner_sha256']==PINS[PLAN/'scan.py'],'plan observation')
scan=json.loads((PLAN/'scan.json').read_bytes());need(scan['status']=='PRELIMINARY_COEFFICIENT_DECOMPOSITION_CLOSURE_NOT_A_BUILD' and scan['decoder_objects_per_side']==123 and scan['mass_objects_per_side']==115 and scan['overlap_objects_per_side']==115,'scan scope/counts')
run=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,timeout=180);need(run.returncode==0 and not run.stderr and run.stdout==(PLAN/'scan.json').read_bytes(),('scan rerun',run.returncode,run.stderr))
opt=subprocess.run([sys.executable,'-O','-I','-S','-B',str(PLAN/'scan.py')],cwd=ROOT,capture_output=True,timeout=30);need(opt.returncode==1 and not opt.stdout and b'optimized Python rejected' in opt.stderr,'optimized scan')
blob=subprocess.run(['git','show','d417147fec:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True,timeout=30).stdout;need(hashlib.sha256(blob).hexdigest()==PINS[SOURCE],'committed source')
imports=['DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.Compact943Decoder','DiophantineConsistency.CompactCoefficientMass'];need([line[7:] for line in SOURCE.read_text().splitlines() if line.startswith('import ')]==imports==scan['source']['imports'] and scan['source']['sha256']==PINS[SOURCE],'source imports')
names=re.findall(r'^#print axioms\s+(\S+)',SOURCE.read_text(),re.M);need(names==['CompactCoefficientDecoder.cast_value','CompactCoefficientDecoder.selector_model','CompactCoefficientDecoder.finite_decomposition'],'exact source report names')
checks=[]
for path,ch,oh,status in AUDITS:
 need(H(path/'CHECK.json')==ch and H(path/'terminal-observation.json')==oh,'audit pin '+str(path));a=json.loads((path/'CHECK.json').read_bytes());o=json.loads((path/'terminal-observation.json').read_bytes())
 need(a['status']==status and type(a['recorded_outer_exit']) is int and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['receipt_sha256']==ch and o['lean_compilations_started']==0,'audit observation '+str(path));checks.append(a)
need(len(scan['audit_receipts'])==2 and all(scan['audit_receipts'][i]['sha256']==AUDITS[i][1] and scan['audit_receipts'][i]['observation_sha256']==AUDITS[i][2] and scan['audit_receipts'][i]['status']==AUDITS[i][3] for i in range(2)),'audit receipt mapping')
canonical=None;results=[]
for side in ('author','peer'):
 d=DEC/side/'lib';m=MASS/side/'lib';dd={p.relative_to(d).as_posix():p for p in d.rglob('*.olean')};mm={p.relative_to(m).as_posix():p for p in m.rglob('*.olean')}
 need(len(dd)==123 and len(mm)==115 and set(mm)<=set(dd) and all(p.is_file() for p in list(dd.values())+list(mm.values()),'overlay inventories '+side)
 rows=scan['objects'][side];need(len(rows)==123 and {r['path'] for r in rows}==set(dd),'recorded decoder inventory '+side)
 for row in rows:
  rel=row['path'];p=dd[rel];need(H(p)==row['sha256'] and str(p.resolve())==row['decoder_resolved'],'decoder object '+side+' '+rel)
  if rel in mm:need(H(mm[rel])==row['sha256'] and str(mm[rel].resolve())==row['mass_resolved'],'same-side overlap '+side+' '+rel)
  else:need('mass_resolved' not in row,'unexpected overlap '+side+' '+rel)
 cur=[(r['path'],r['sha256']) for r in rows]
 if canonical is None:canonical=cur
 else:need(cur==canonical,'corresponding decoder sides')
 for idx,(module,prefix) in enumerate((('Compact943Decoder',DEC),('CompactCoefficientMass',MASS))):
  source=prefix/side/(module+'.olean');matches=[x for x in scan['seeds'] if x['side']==side and x['module']==module];need(len(matches)==1,'seed row '+side+' '+module);seed=matches[0];receipt=next(x for x in checks[idx]['runs'] if x['side']==side)
  need(source.is_file() and str(source)==seed['path'] and str(source.resolve())==seed['resolved'] and H(source)==seed['sha256']==receipt['object_sha256'],'seed object '+side+' '+module)
  need(slots(source.with_suffix(''))==seed['source_slots'] and [s for s,v in seed['source_slots'].items() if v is not None]==['.olean'],'seed source companions '+side+' '+module)
  target=slots(d/'DiophantineConsistency'/module);need(target==scan['companion_slots'][side+'/'+module] and all(v is None for v in target.values()),'seed target '+side+' '+module)
 target=slots(d/'DiophantineConsistency/CompactCoefficientDecoder');need(target==scan['companion_slots'][side+'/CompactCoefficientDecoder'] and all(v is None for v in target.values()),'client target '+side)
 direct=slots(d/'DiophantineConsistency/ArithmeticWindowCarry');need(direct==scan['companion_slots'][side+'/ArithmeticWindowCarry'] and direct['.olean'] is not None,'carry direct '+side)
 results.append({'side':side,'decoder_objects':len(dd),'mass_objects':len(mm),'matched_overlap':len(mm),'seed_objects_checked':2})
need(len(scan['seeds'])==4 and len(scan['companion_slots'])==8,'seed and target guard count')
init=slots(PACKAGE/'Init');need(init==scan['package_init_slots'] and {k for k,v in init.items() if v is not None}=={'.olean','.olean.private','.olean.server','.ir'},'package Init slots')
print(json.dumps({'status':'PASS_INDEPENDENT_COEFFICIENT_DECOMPOSITION_CLOSURE','reviewed_commit':'28622c2888','scan_sha256':PINS[PLAN/'scan.json'],'source_sha256':PINS[SOURCE],'same_side_inventories':results,'audited_seed_objects':4,'seed_source_companion_slots':40,'target_and_carry_slots':80,'init_slots':10,'source_report_names':names,'normal_scan_exit':0,'optimized_scan_exit':1,'scope':'Point-in-time source/provider and seed review; neither parent audit rerun nor paired build. Finite identity has arbitrary model-valued f,b; graph-column equality, Boolean/NoCarry, retained K, decoder application, machine and internal iPRA remain open.'},indent=2,sort_keys=True))
