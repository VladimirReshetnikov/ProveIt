#!/usr/bin/env python3
"""Point-in-time twelve-source common-period same-side closure."""
import hashlib,json,os,re,subprocess
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('optimized Python rejected')
REPO=Path.cwd();ROOT=REPO/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';REVIEWS=ROOT/'reviews';PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PREFIX=Path('/tmp/ipra-direct-symbolic-k-pair-01')
SAME=BASE/'compact44-same-witness-saturation-closure-plan/scan.json';PERIOD=BASE/'compact44-period-copy-closure-plan/scan.json';AUDIT=REVIEWS/'compact44-direct-symbolic-k-pair-independent-audit/CHECK.json';OBS=AUDIT.parent/'terminal-observation.json';SP=BASE/'compact44-selector-period-prototype/CompactSelectorPeriod.lean';COMMON=BASE/'compact44-common-period-bits-prototype/CompactCommonPeriodBits.lean'
PINS={SAME:'ca42e7393f09055f77ace4c327319d66a8478dbfc9607ddc8af67eda652ec934',PERIOD:'82233aae5f3b13169be66b350d9dae951111177756f24b1e8bbe143239028771',AUDIT:'5aecb3c05962fd5f13650899bac9ce6f2406827a8d08f43714ddd2966716a634',OBS:'51feb6dba903581ab36824efa3c816a4b4e6c2d8b44d63030e0971acf82f73a3',SP:'1b01e1c5585ecab636d94624d670354e659eb85bb219f44a482d28114c79a492',COMMON:'23ab0a6d005f15336abbeae3703ad761979b5fb91eb4def6eee20c6ff75b3711'}
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def inventory(stem):
 out={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):need(p.is_file(),('nonregular',str(p)));out[str(p)]={'resolved':str(p.resolve()),'sha256':h(p)}
  else:out[str(p)]=None
 return out
for p,sha in PINS.items():need(p.is_file() and h(p)==sha,('fixed input drift',str(p)))
a=json.loads(AUDIT.read_bytes());o=json.loads(OBS.read_bytes());need(a['status']=='PASS_INDEPENDENT_DIRECT_SYMBOLIC_K_PAIR_AUDIT' and type(a['recorded_outer_exit']) is int and a['recorded_outer_exit']==0 and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==PINS[AUDIT],'bad parent audit schema')
same=json.loads(SAME.read_bytes())['source_order'];period=json.loads(PERIOD.read_bytes())['source_order'];rows=same+period[:4]+period[7:]
for n,p,c in [('CompactSelectorPeriod',SP,'322641bfc9'),('CompactCommonPeriodBits',COMMON,'2e9283a99a')]:rows.append({'module':'DiophantineConsistency.'+n,'source':str(p),'source_sha256':PINS[p],'source_commit':c})
need(len(rows)==12 and len({x['module'] for x in rows})==12,'module count')
available=set();sources=[];external=set()
for row in rows:
 p=Path(row['source']);need(p.is_file() and h(p)==row['source_sha256'],('source drift',str(p)));old=subprocess.run(['git','show',f'{row["source_commit"]}:{p.relative_to(REPO)}'],capture_output=True,check=True,timeout=15).stdout;need(hashlib.sha256(old).hexdigest()==row['source_sha256'],('git source mismatch',str(p)))
 imports=[x[7:] for x in p.read_text().splitlines() if x.startswith('import ')];need(imports==row.get('imports',imports),('imports mismatch',str(p)));names=re.findall(r'^#print axioms\s+([^\s]+)',p.read_text(),re.M);need(len(names)>0 and len(names)==len(set(names)),('axiom names',str(p)))
 for dep in imports:
  if dep not in available:need(not any(x['module']==dep for x in rows),('out-of-order',row['module'],dep));external.add(dep)
 sources.append({'module':row['module'],'source':str(p),'source_commit':row['source_commit'],'source_sha256':h(p),'imports':imports,'axiom_reports':names});available.add(row['module'])
expected={'DiophantineConsistency.ArithmeticModularCancellation','DiophantineConsistency.CompactGraphDerivedRadix','DiophantineConsistency.CompactHighResidue','DiophantineConsistency.CompactLowEven','DiophantineConsistency.CompactLowExact','DiophantineConsistency.CompactMixedIncrement','DiophantineConsistency.CompactSymbolicKernel','DiophantineConsistency.FreeJConcreteDigitsClient'};need(external==expected,('external set',external))
objects={};targets={};direct={};prior=None
for side in ('author','peer'):
 lib=PREFIX/side/'lib';files={p.relative_to(lib):p for p in lib.rglob('*.olean')};need(len(files)==150,('object count',side,len(files)));canonical=[]
 for rel,p in sorted(files.items()):canonical.append({'path':str(rel),'sha256':h(p),'resolved':str(p.resolve())})
 compare=[(r['path'],r['sha256']) for r in canonical]
 if prior is None:prior=compare
 else:need(compare==prior,'author peer provider mismatch')
 objects[side]=canonical
 for row in sources:
  stem=lib/Path(*row['module'].split('.'));inv=inventory(stem);need(not any(inv.values()),('target collision',side,row['module']));targets.update(inv)
 for name in sorted(external):
  stem=lib/Path(*name.split('.'));inv=inventory(stem);need(inv[str(stem)+'.olean'] is not None,('missing direct object',side,name));direct.update(inv)
init=inventory(PACKAGE/'Init');need(init[str(PACKAGE/'Init.olean')] is not None,'missing Init');need(len(targets)==240 and len(direct)==160 and len(init)==10,'slot counts')
print(json.dumps({'status':'PRELIMINARY_COMMON_PERIOD_TWELVE_SOURCE_CLOSURE_NOT_A_BUILD','parent_audit_sha256':h(AUDIT),'source_order':sources,'objects':objects,'external_direct_slots':direct,'target_slots':targets,'init_slots':init,'scope':'Point-in-time source and provider inventory only; same graph-derived witnesses under fixed-symbolic graph zero and positive coordinates, arbitrary K. No retained K/port binding, weighted column, decoder NoCarry, machine or iPRA theorem.'},indent=2,sort_keys=True))
