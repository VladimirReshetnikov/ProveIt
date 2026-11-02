#!/usr/bin/env python3
"""Read-only, point-in-time decoder/coefficient same-side closure inventory."""
import hashlib,json,os,subprocess
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
ROOT=Path.cwd()/'Computability/DiophantineConsistency'; BASE=ROOT/'research/ordinary12-ipra-bridge'; REVIEWS=ROOT/'reviews'
SOURCE=BASE/'compact44-coefficient-decomposition-prototype/CompactCoefficientDecoder.lean'
AUDITS=[(REVIEWS/'compact44-943-decoder-independent-audit','5a6695bd9fe61ae0d04331170eef880aa0bbea185b5dc3227950fc812877d578','5a29da0ea330d1781372fd5d2c8fd22c36a87eaa215b315720c087400d3618d3','PASS_INDEPENDENT_COMPACT_943_DECODER_AUDIT'),(REVIEWS/'compact44-coefficient-mass-independent-audit','9fc48750f7846e6f2b5cfe3ea93b14935720fd04115b45e8cbf276b02af92a55','86e0753623b1f8d7ce2e0c0134e02e84430eccf53174d580f0de477e836b87e7','PASS_INDEPENDENT_COMPACT44_COEFFICIENT_MASS_AUDIT')]
DEC=Path('/tmp/ipra-compact943-decoder-pair-01');MASS=Path('/tmp/ipra-compact-coefficient-mass-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def inv(stem):
 result={}
 for suf in SUFFIXES:
  p=Path(str(stem)+suf)
  if os.path.lexists(p):
   need(p.is_file(),('not regular file',str(p)));result[suf]={'realpath':str(p.resolve()),'sha256':h(p)}
  else:result[suf]=None
 return result
need(h(SOURCE)=='86f9ddd083eb5767359a691774c76c88a5e7c1627dc693f474880a78e32a03c8','source drift')
rel=SOURCE.relative_to(Path.cwd());old=subprocess.run(['git','show',f'd417147fec:{rel}'],capture_output=True,check=True,timeout=15).stdout
need(hashlib.sha256(old).hexdigest()==h(SOURCE),'source differs from committed bytes')
imports=[line[7:] for line in SOURCE.read_text().splitlines() if line.startswith('import ')]
need(imports==['DiophantineConsistency.ArithmeticWindowCarry','DiophantineConsistency.Compact943Decoder','DiophantineConsistency.CompactCoefficientMass'],'imports drift')
receipts=[]
for path,ch,oh,status in AUDITS:
 check=path/'CHECK.json';obs=path/'terminal-observation.json';need(h(check)==ch and h(obs)==oh,'audit or observation drift')
 c=json.loads(check.read_bytes());o=json.loads(obs.read_bytes());need(c['status']==status and type(c['recorded_outer_exit']) is int and c['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['receipt_sha256']==ch and o['lean_compilations_started']==0,'audit schema mismatch');receipts.append(c)
objects={};seeds=[];slots={};common=None
for side in ('author','peer'):
 d=DEC/side/'lib';m=MASS/side/'lib';dd={p.relative_to(d):p for p in d.rglob('*.olean')};mm={p.relative_to(m):p for p in m.rglob('*.olean')}
 need(len(dd)==123 and len(mm)==115 and set(mm)<=set(dd),('provider inventory',side,len(dd),len(mm)))
 commonrows=[]
 for rel in sorted(dd):
  dp=dd[rel];hd=h(dp);row={'path':str(rel),'sha256':hd,'decoder_resolved':str(dp.resolve())}
  if rel in mm:
   need(h(mm[rel])==hd,('overlap mismatch',side,str(rel)));row['mass_resolved']=str(mm[rel].resolve())
  commonrows.append(row)
 objects[side]=commonrows
 canonical=[(x['path'],x['sha256']) for x in commonrows]
 if common is None:common=canonical
 else:need(canonical==common,'author peer decoder providers differ')
 for n,prefix,receipt in [('Compact943Decoder',DEC,receipts[0]),('CompactCoefficientMass',MASS,receipts[1])]:
  p=prefix/side/(n+'.olean');r=next(x for x in receipt['runs'] if x['side']==side)
  need(p.is_file() and h(p)==r['object_sha256'],('seed differs from audited output',side,n));seeds.append({'side':side,'module':n,'path':str(p),'resolved':str(p.resolve()),'sha256':h(p),'source_slots':inv(p.with_suffix(''))})
  need([k for k,v in seeds[-1]['source_slots'].items() if v is not None]==['.olean'],('unexpected seed companion',side,n))
  need(not any(inv((d/'DiophantineConsistency'/n)).values()),('seed target collision',side,n))
  slots[f'{side}/{n}']=inv(d/'DiophantineConsistency'/n)
 slots[f'{side}/CompactCoefficientDecoder']=inv(d/'DiophantineConsistency/CompactCoefficientDecoder')
 need(not any(slots[f'{side}/CompactCoefficientDecoder'].values()),('output collision',side))
 slots[f'{side}/ArithmeticWindowCarry']=inv(d/'DiophantineConsistency/ArithmeticWindowCarry')
 need(slots[f'{side}/ArithmeticWindowCarry']['.olean'] is not None,('missing direct object',side))
init=inv(PACKAGE/'Init');need(init['.olean'] is not None,'missing Init')
print(json.dumps({'status':'PRELIMINARY_COEFFICIENT_DECOMPOSITION_CLOSURE_NOT_A_BUILD','source':{'path':str(SOURCE),'sha256':h(SOURCE),'source_commit':'d417147fec','imports':imports},'audit_receipts':[{'check':str(p/'CHECK.json'),'sha256':ch,'observation_sha256':oh,'status':st} for p,ch,oh,st in AUDITS],'decoder_objects_per_side':123,'mass_objects_per_side':115,'overlap_objects_per_side':115,'objects':objects,'seeds':seeds,'companion_slots':slots,'package_init_slots':init,'scope':'Point-in-time same-side inventory, not a frozen build or complete package/transitive ancestry authentication.'},indent=2,sort_keys=True))
