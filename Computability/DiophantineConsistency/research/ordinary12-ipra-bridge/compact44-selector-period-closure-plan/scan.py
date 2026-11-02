#!/usr/bin/env python3
"""Provisional read-only selector-period source/provider inventory."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';SOURCE=BASE/'compact44-selector-period-prototype/CompactSelectorPeriod.lean';E=BASE/'compact44-selector-graph-pair-prototype/evidence';PARENT=Path('/tmp/ipra-selector-graph-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(SOURCE)=='1b01e1c5585ecab636d94624d670354e659eb85bb219f44a482d28114c79a492'
blob=subprocess.run(['git','show','322641bfc9:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(SOURCE)
assert [s[7:] for s in SOURCE.read_text().splitlines() if s.startswith('import ')]==['DiophantineConsistency.CompactSelectorGraph']
assert re.findall(r'^#print axioms\s+(\S+)',SOURCE.read_text(),re.M)==['CompactSelectorPeriod.period_index_zero_allowed','CompactSelectorPeriod.fixed_graph_period_selectors']
assert H(E/'receipt.json')=='3478cdb0597c6b2e86df02f58e3210c932b954e591338382a7cb4f6b06495a16' and H(E/'terminal-observation.json')=='003533e641317567bcd796ead6a318fd85d0a07f96dd587e586c9d3249dbe875'
r=json.loads((E/'receipt.json').read_bytes());o=json.loads((E/'terminal-observation.json').read_bytes());assert r['status']=='PASS_PAIRED_SELECTOR_GRAPH' and type(o['observed_exit']) is int and o['observed_exit']==0 and o['session_id']==72622 and o['receipt_sha256']==H(E/'receipt.json') and o['lean_processes_remaining'] is False
assert (PARENT/'receipt.json').read_bytes()==(E/'receipt.json').read_bytes();libs=[PARENT/s/'lib' for s in ('author','peer')];inv=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs];assert set(inv[0])==set(inv[1]) and len(inv[0])==150
objects=[]
for rel in sorted(inv[0]):
 a,b=inv[0][rel],inv[1][rel];assert H(a)==H(b);objects.append({'path':rel,'sha256':H(a),'author_resolved':str(a.resolve()),'peer_resolved':str(b.resolve())})
def slots(stem):
 result={}
 for suffix in SUFFIXES:
  p=Path(str(stem)+suffix)
  if os.path.lexists(p):
   assert p.is_file(),str(p);result[str(p)]={'sha256':H(p),'realpath':str(p.resolve())}
  else:result[str(p)]=None
 return result
direct={};targets={}
for lib in libs:
 stem=lib/'DiophantineConsistency/CompactSelectorGraph';assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem));stem=lib/'DiophantineConsistency/CompactSelectorPeriod';z=slots(stem);assert all(v is None for v in z.values());targets.update(z)
init=slots(PACKAGE/'Init');assert Path(str(PACKAGE/'Init')+'.olean').is_file()
print(json.dumps({'status':'PROVISIONAL_SELECTOR_PERIOD_SOURCE_CLOSURE_NOT_A_BUILD','source':str(SOURCE),'source_commit':'322641bfc9','source_sha256':H(SOURCE),'imports':['DiophantineConsistency.CompactSelectorGraph'],'axiom_reports':['CompactSelectorPeriod.period_index_zero_allowed','CompactSelectorPeriod.fixed_graph_period_selectors'],'parent_receipt_sha256':H(E/'receipt.json'),'parent_independent_audit':'PENDING','objects':objects,'direct_slots':direct,'target_slots':targets,'init_slots':init,'scope':'Point-in-time source and provisionally paired parent inventory only; no parent artifact audit rerun, build, retained byte/tuple binding, full decoder, machine or iPRA proof.'},indent=2,sort_keys=True))
