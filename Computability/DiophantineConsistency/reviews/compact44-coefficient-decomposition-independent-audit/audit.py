#!/usr/bin/env python3
"""Independent no-Lean check of the two-side coefficient artifacts."""
import hashlib,importlib.util,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';P=BASE/'compact44-coefficient-decomposition-pair-prototype';E=P/'evidence';OUT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01');PROVIDER=Path('/tmp/ipra-compact943-decoder-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();r=json.loads((E/'receipt.json').read_bytes());obs=json.loads((E/'terminal-observation.json').read_bytes());assert H(E/'receipt.json')=='0639b6374ef84aaa014d67552109bad80758d5f41b38010cdd63f19ce526fbc8' and (E/'receipt.json').read_bytes()==(OUT/'receipt.json').read_bytes()
for f in (E/'receipt.json',E/'terminal-observation.json',E/'author/compiler.log',E/'peer/compiler.log'):
 q=subprocess.run(['git','show','649a10beea:'+f.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True);assert q.stdout==f.read_bytes(),str(f)
assert obs['session_id']==43151 and type(obs['observed_exit']) is int and obs['observed_exit']==0 and obs['lean_processes_remaining'] is False and obs['receipt_sha256']==H(E/'receipt.json') and obs['protected_head']=='89303c9fc5e0ff51c3462c4f1589bb33762965e3'
assert r['status']=='PASS_PAIRED_COEFFICIENT_DECOMPOSITION' and r['protected_head']==obs['protected_head'] and r['driver_sha256']=='604bf5a6e45bc2852fbff3482684479b52517e814503a48617626ff28e0505bf' and H(P/'replay.py')==r['driver_sha256']
sp=importlib.util.spec_from_file_location('driver',P/'replay.py');d=importlib.util.module_from_spec(sp);sp.loader.exec_module(d)
for p,h in (d.PINS|d.CLOSURE_PINS).items():assert H(p)==h,str(p)
scan=json.loads((d.PLAN/'scan.json').read_bytes());assert r['parents']==[json.loads((a/'CHECK.json').read_bytes()) for a in d.AUDITS]
src=OUT/'frozen/DiophantineConsistency/CompactCoefficientDecoder.lean';assert src.is_file() and not src.is_symlink() and H(src)==H(d.SOURCE)=='86f9ddd083eb5767359a691774c76c88a5e7c1627dc693f474880a78e32a03c8'
expected_names={'CompactCoefficientDecoder.cast_value','CompactCoefficientDecoder.selector_model','CompactCoefficientDecoder.finite_decomposition'};allstems={PACKAGE/'Init'};rows=[]
assert len(r['runs'])==2
for side,item in zip(('author','peer'),r['runs']):
 assert item['side']==side and type(item['compiler_exit']) is int and item['compiler_exit']==0 and item['stop_reason'] is None
 lib=OUT/side/'lib';base=PROVIDER/side/'lib';old={p.relative_to(base).as_posix():p for p in base.rglob('*.olean') if p.is_file()};new={p.relative_to(lib).as_posix():p for p in lib.rglob('*.olean') if p.is_file()};assert len(old)==123
 additions={'DiophantineConsistency/Compact943Decoder.olean','DiophantineConsistency/CompactCoefficientMass.olean','DiophantineConsistency/CompactCoefficientDecoder.olean'};assert set(new)==set(old)|additions
 for rel,path in old.items():assert H(path)==H(new[rel]),(side,rel)
 for module in ('Compact943Decoder','CompactCoefficientMass'):
  seeds=[x for x in scan['seeds'] if x['side']==side and x['module']==module];assert len(seeds)==1;z=seeds[0];origin=Path(z['path']);target=lib/'DiophantineConsistency'/(module+'.olean');assert origin.is_file() and target.is_file() and not target.is_symlink() and H(origin)==H(target)==z['sha256'];allstems|={Path(str(origin)[:-6]),Path(str(target)[:-6])}
 obj=lib/'DiophantineConsistency/CompactCoefficientDecoder.olean';log=OUT/side/'compiler.log';saved=E/side/'compiler.log';assert obj.is_file() and not obj.is_symlink() and H(obj)==item['object_sha256']=='aeef5ca3e389d89d84fc494e1b4d1fa02d1cd9cf5578943cd07d98e242406a07';assert log.read_bytes()==saved.read_bytes() and H(log)==item['log_sha256'] and log.read_text()==item['stdout']
 assert not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',item['stdout'])
 reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",item['stdout'],re.M);assert len(reports)==3 and {n for n,_ in reports}==expected_names and all({a.strip() for a in ax.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,ax in reports)
 window=lib/'DiophantineConsistency/ArithmeticWindowCarry.olean';expected={str(PACKAGE/'Init.olean'),str(window),str(lib/'DiophantineConsistency/Compact943Decoder.olean'),str(lib/'DiophantineConsistency/CompactCoefficientMass.olean')};lines=item['deps_stdout'].splitlines();assert set(lines)==expected and 1<=lines.count(str(PACKAGE/'Init.olean'))<=2 and all(lines.count(x)==1 for x in expected if x!=str(PACKAGE/'Init.olean'))
 assert item['command']==[str(d.LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(src),'-o',str(obj)]
 allstems|={Path(str(obj)[:-6]),Path(str(window)[:-6])};rows.append({'side':side,'inherited_objects_checked':len(old),'object_sha256':H(obj),'sampled_peak_rss_bytes':item['sampled_peak_rss_bytes']})
assert len(allstems)==13;guards=r['guards'];assert set(guards)=={str(stem)+s for stem in allstems for s in d.SUFFIXES} and len(guards)==130
for name,prior in guards.items():
 p=Path(name)
 if prior is None:assert not os.path.lexists(p),name
 else:assert p.is_file() and str(p.resolve())==prior['realpath'] and H(p)==prior['sha256'],name
print(json.dumps({'status':'PASS_INDEPENDENT_COEFFICIENT_DECOMPOSITION_PAIR_AUDIT','evidence_commit':'649a10beea','receipt_sha256':H(E/'receipt.json'),'recorded_outer_session':43151,'recorded_outer_exit':0,'runs':rows,'same_side_seed_copies':4,'guard_slots':130,'lean_launched':False,'scope':'IΣ₁-model finite external-index coefficient identity for arbitrary f and b; no Boolean or NoCarry assumption, graph-column identification, retained-K binding, machine simulation or internal iPRA proof.'},indent=2))
