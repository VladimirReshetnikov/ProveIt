#!/usr/bin/env python3
"""Point-in-time same-provider partial-band source closure; no Lean."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';SOURCE=RESEARCH/'compact44-partial-band-prototype/CompactPartialBand.lean';AUDIT=BASE/'reviews/compact44-coefficient-decomposition-independent-audit';PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(SOURCE)=='26b73b92c91baef599ab9d473965af940b9b39ae81d76f0979ed80129109ba0f'
blob=subprocess.run(['git','show','7dea2a8f40:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout;assert hashlib.sha256(blob).hexdigest()==H(SOURCE)
imports=[line[7:] for line in SOURCE.read_text().splitlines() if line.startswith('import ')];assert imports==['DiophantineConsistency.CompactCoefficientDecoder','DiophantineConsistency.ArithmeticCyclicWord']
names=re.findall(r'^#print axioms\s+(\S+)',SOURCE.read_text(),re.M);assert names==['CompactPartialBand.band_decomposition']
assert H(AUDIT/'audit.py')=='389e92b0a29c342e39b0f9ad2fd6b4e2d7e42245433ceda24a613670492c55ff' and H(AUDIT/'CHECK.json')=='2351c55148f2e3eb4b8ac51894050dbfd942eef7fdad26030251cbf637e94432' and H(AUDIT/'terminal-observation.json')=='05ee4dbdf225dca03ed312273d325942f45e6770878cb3f6ba341fa34093a665'
a=json.loads((AUDIT/'CHECK.json').read_bytes());o=json.loads((AUDIT/'terminal-observation.json').read_bytes());assert a['status']=='PASS_INDEPENDENT_COEFFICIENT_DECOMPOSITION_PAIR_AUDIT' and type(o['observed_exit']) is int and o['observed_exit']==0 and o['lean_launched'] is False and o['check_sha256']==H(AUDIT/'CHECK.json')
libs=[PARENT/side/'lib' for side in ('author','peer')];inv=[{p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()} for lib in libs];assert set(inv[0])==set(inv[1]) and len(inv[0])==126
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
 for module in ('CompactCoefficientDecoder','ArithmeticCyclicWord'):
  stem=lib/'DiophantineConsistency'/module;assert Path(str(stem)+'.olean').is_file();direct.update(slots(stem))
 stem=lib/'DiophantineConsistency/CompactPartialBand';z=slots(stem);assert all(v is None for v in z.values());targets.update(z)
init=slots(PACKAGE/'Init');assert Path(str(PACKAGE/'Init')+'.olean').is_file()
assert len(direct)==40 and len(targets)==20 and len(init)==10
print(json.dumps({'status':'PRELIMINARY_PARTIAL_BAND_SOURCE_CLOSURE_NOT_A_BUILD','source':str(SOURCE),'source_commit':'7dea2a8f40','source_sha256':H(SOURCE),'imports':imports,'axiom_reports':names,'parent_audit_sha256':H(AUDIT/'CHECK.json'),'objects':objects,'direct_slots':direct,'target_slots':targets,'init_slots':init,'scope':'Point-in-time same-side source/provider inventory only; no parent audit rerun or paired build, graph-derived full column, retained K binding, NoCarry, machine or iPRA proof.'},indent=2,sort_keys=True))
