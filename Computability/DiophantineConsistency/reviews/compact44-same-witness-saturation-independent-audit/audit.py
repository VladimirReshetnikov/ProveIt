#!/usr/bin/env python3
import hashlib,importlib.util,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';P=BASE/'compact44-same-witness-saturation-pair-prototype';E=P/'evidence';OUT=Path('/tmp/ipra-same-witness-saturation-pair-01');PARENT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();r=json.loads((E/'receipt.json').read_bytes());obs=json.loads((E/'terminal-observation.json').read_bytes());assert (E/'receipt.json').read_bytes()==(OUT/'receipt.json').read_bytes()
assert obs['observed_exit']==0 and obs['session_id']==53165 and obs['receipt_sha256']==H(E/'receipt.json') and obs['protected_head']==r['protected_head']
assert H(E/'receipt.json')=='31b5d6d1cc64af56e08db375c20a1d67e5cd26590ef447b31ea3d43f17a82aee'
for f in [E/'receipt.json',E/'terminal-observation.json']+list((E/'author').glob('*.log'))+list((E/'peer').glob('*.log')):
 q=subprocess.run(['git','show','1013f63c58:'+f.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True);assert q.stdout==f.read_bytes(),str(f)
assert r['status']=='PASS_PAIRED_SAME_WITNESS_SATURATION' and r['protected_head']=='398225c1ee977f8be363d88f6338b61aa878d902'
sp=importlib.util.spec_from_file_location('candidate',P/'replay.py');d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d);assert H(P/'replay.py')==r['driver_sha256'];assert r['fixed_pins']=={str(p):h for p,h in d.PINS.items()}
for p,h in d.PINS.items():assert H(p)==h,str(p)
scan=json.loads((d.PLAN/'scan.json').read_bytes());parent=json.loads((d.PARENT_AUDIT/'CHECK.json').read_bytes());assert r['parent_audit']==parent
assert [z['module'] for z in scan['source_order']]==d.MODULES
allstems={PACKAGE/'Init'};runs=[]
for side,run in zip(('author','peer'),r['runs']):
 assert run['side']==side and len(run['steps'])==3
 lib=OUT/side/'lib';base=PARENT/side/'lib';old={p.relative_to(base).as_posix():p for p in base.rglob('*.olean') if p.is_file()};new={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};assert len(old)==143
 expectednew={Path(*name.split('.')).with_suffix('.olean').as_posix() for name in d.MODULES};assert set(new)==set(old)|expectednew
 for rel,p in old.items():assert H(p)==H(new[rel]),(side,rel)
 for item,source in zip(run['steps'],scan['source_order']):
  module=item['module'];assert module==source['module'] and item['compiler_exit']==0 and item['deps_exit']==0 and item['stop_reason'] is None
  src=(OUT/'frozen'/Path(*module.split('.'))).with_suffix('.lean');obj=(lib/Path(*module.split('.'))).with_suffix('.olean');log=OUT/side/(module.replace('.','_')+'.log');saved=E/side/(module.replace('.','_')+'.log')
  assert src.is_file() and not src.is_symlink() and H(src)==source['source_sha256']==item['source_sha256'] and H(source['source'])==item['source_sha256']
  assert obj.is_file() and not obj.is_symlink() and H(obj)==item['object_sha256']
  assert saved.read_bytes()==log.read_bytes() and H(log)==item['log_sha256'] and log.read_text()==item['stdout']
  assert not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',item['stdout'])
  reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",item['stdout'],re.M);names={
   d.MODULES[0]:{'FreeJGraphCongruenceExplore.'+x for x in ('fixed_symbolic_aligned','symbolic_aligned','first_pair_mod','graph_congruence','graph_aligned_congruence')},
   d.MODULES[1]:{'CompactSymbolicGraphSaturation.graph_saturation'},
   d.MODULES[2]:{'CompactSameWitnessSaturation.fixed_graph_saturation','CompactSameWitnessSaturation.generic_graph_saturation'}}
  assert len(reports)==len(names[module]) and {n for n,_ in reports}==names[module] and all({a.strip() for a in axioms.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,axioms in reports) and [list(x) for x in reports]==item['axiom_reports']
  expected={str(PACKAGE/'Init.olean')}|{str((lib/Path(*name.split('.'))).with_suffix('.olean')) for name in source['imports']};lines=item['deps_stdout'].splitlines();assert set(lines)==expected and 1<=lines.count(str(PACKAGE/'Init.olean'))<=2 and all(lines.count(x)==1 for x in expected if x!=str(PACKAGE/'Init.olean'))
  assert item['command']==[str(d.LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(src),'-o',str(obj)]
  allstems.add(Path(str(obj)[:-6]));allstems.update(Path(x[:-6]) for x in expected)
  runs.append({'side':side,'module':module,'object_sha256':H(obj),'axiom_names':sorted(x[0] for x in reports),'sampled_peak_rss_bytes':item['sampled_peak_rss_bytes']})
assert len(allstems)==19;guards=r['guards'];assert set(guards)=={str(stem)+suffix for stem in allstems for suffix in d.SUFFIXES} and len(guards)==190
for name,value in guards.items():
 p=Path(name)
 if value is None:assert not os.path.lexists(p),name
 else:assert p.is_file() and str(p.resolve())==value['realpath'] and H(p)==value['sha256'],name
print(json.dumps({'status':'PASS_INDEPENDENT_SAME_WITNESS_PAIR_ARTIFACT_AUDIT','receipt_sha256':H(E/'receipt.json'),'recorded_outer_session':53165,'recorded_outer_exit':0,'runs':runs,'inherited_objects_per_side':143,'guard_slots':190,'lean_launched':False,'scope':'For positive variables and the fixed symbolic beta/masks with arbitrary natural K, one common model N,w satisfy the stated alignment, congruence, digit bounds and two global no-carry relations. No retained K-byte binding, weighted-word carry premises, decoder, machine equivalence or iPRA proof. Parent/package/transitive/dynamic, resource and between-check limitations remain.'},indent=2))
