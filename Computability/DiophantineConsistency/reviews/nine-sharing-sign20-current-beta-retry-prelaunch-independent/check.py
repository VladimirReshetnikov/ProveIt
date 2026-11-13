#!/usr/bin/env python3
"""Review current-beta proof source and exact expression provider without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign20-current-beta-retry-check';draft=research/'nine-sharing-sign20-current-beta-retry-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json';assert sha(manifest)=='1c10ba04ea20e09fd775fbe0ff2a7a893c0763cbad0b607cfa833fe094cec3e8';entry,=json.loads(manifest.read_text())['rows'];assert entry['module']=='DiophantineConsistency.Sign20CurrentBeta'
src=packet/'src/DiophantineConsistency/Sign20CurrentBeta.lean';s=src.read_text();assert sha(src)==sha(draft/'Sign20CurrentBeta.lean')==entry['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign20CurrentExpressionDef']
assert 'theorem positive : (0 : ℤ) < CurrentWindowCarry2011.ports 0' in s and 'theorem nonzero : CurrentWindowCarry2011.ports 0 ≠ 0 := ne_of_gt positive' in s
assert 'set_option maxHeartbeats 4000000 in' in s and 'one_lt_pow₀' in s and 'unfold CurrentMasks2011.beta; omega' in s
old=(research/'nine-sharing-seed38-current-jones-retry01/src/DiophantineConsistency/SharingSeed38CurrentJones.lean').read_text();proof=s.split('theorem positive :',1)[1].split('\ntheorem nonzero',1)[0];oldproof=old.split('theorem current_beta_positive :',1)[1].split('\ntheorem ',1)[0].strip();assert proof.strip()==oldproof
failed=(research/'nine-sharing-sign20-current-beta-draft/Sign20CurrentBeta.lean').read_text()
assert s.replace('by unfold CurrentMasks2011.radix; decide : 1 < CurrentMasks2011.radix','by decide : 1 < CurrentMasks2011.radix')==failed
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-current-beta-failure-independent/check.py')],check=True,capture_output=True,timeout=120)
runner=packet/'run.py';assert sha(runner)=='8e9abac5facbeb2a4c15a6a594063c8d5dcc0e703a052a79a05cf608c446d274';r=runner.read_text();assert "elif local=='Sign20CurrentExpressionDef':" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(check_expression()==expression_data,'expression final drift')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-expression-eval-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'scope':'current port beta positivity/nonzero source proposal; no Lean theorem or external-byte binding'},indent=2,sort_keys=True))
