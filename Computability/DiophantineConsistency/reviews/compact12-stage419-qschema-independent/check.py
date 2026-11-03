#!/usr/bin/env python3
"""Check the exact QSchema repair, cone change, and two stage receipts."""
from hashlib import sha256
import json
import os
from pathlib import Path
import sys

if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1];B=D/'research/ordinary12-ipra-bridge'
OLD=B/'compact12-ipra-expanded-cone-rebuild-stage317-source-retry/cone-repinned.json'
NEW=B/'compact12-ipra-expanded-cone-rebuild-stage419-source-retry/cone-repinned.json'
FAILED=B/'compact12-ipra-expanded-cone-rebuild-stage419/observations/batch-084/stage-0419'
PASSED=B/'compact12-ipra-expanded-cone-rebuild-stage419-source-retry/observations/batch-084/stage-0419'
SOURCE=ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/QSchema.lean'
SAVED=NEW.parent/'corrected-source.lean'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB=Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
PINS={OLD:'eb5a8a3c8efb7b1d936d4c77ba2c6d201aff6d03f23c9e1697dd2b518aefcbf2',
 NEW:'b5eb6a00e30599c49a851b38746582c75f1eaba2e6c9a66ed6a8adec9f4dc424',
 FAILED/'terminal.json':'e767354a4e1bc253cb0dde92ea4a72d5ef1fb42f2d4a2f73c6797047510e941f',
 PASSED/'terminal.json':'217c73fc4c9f82c75351021ca070c456e4e7b60b25b03e77973869237e5b7407',
 FAILED/'source.lean':'80c040905d9d0565f17f6cce8d8036549096088fc2a3559d9c7f6f752b8caa0a',
 SOURCE:'0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1',
 SAVED:'0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1',
 PASSED/'source.lean':'0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1',
 FAILED/'compile.log':'028258a888e8d7c81c61b543c5a6a888988ceb6fcf51bd41b874c1b8213d2b6d',
 PASSED/'compile.log':'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 FAILED/'deps':'ffd4bd16d2480a4b93629a00079598dab8048ab9fc2e4aa859d78e604004c82f',
 PASSED/'deps':'ffd4bd16d2480a4b93629a00079598dab8048ab9fc2e4aa859d78e604004c82f',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
SUFFIX=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
def need(x,m):
 if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'dangling/non-file: '+str(p))
 return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
old_source=(FAILED/'source.lean').read_text();new_source=SOURCE.read_text()
statement='''theorem consistent_ZF_of_native (h : qTheory.Consistent V) :
    (𝗭𝗙 : SetTheory).Consistent V :='''
old=statement+'''
  InternalInterpretation.consistent_of_falsum_transfer provable_falsum_native_of_ZF h'''
new=statement+''' by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : V) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZF
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at hZF ⊢
  exact provable_falsum_native_of_ZF hZF'''
need(old_source.count(old)==1 and old_source.replace(old,new,1)==new_source,'source edit exceeds intended proof replacement')
need('sorry' not in new and 'admit' not in new and 'axiom' not in new,'repair contains placeholder')
a=json.loads(OLD.read_text());b=json.loads(NEW.read_text());name='ZFCinPA.QSchema'
need(set(b)-set(a)=={'stage419_source_correction'} and not set(a)-set(b),'cone keys')
need(all(a[k]==b[k] for k in a if k!='candidate_sources'),'unrelated cone field changed')
need(set(a['candidate_sources'])==set(b['candidate_sources']) and len(b['candidate_sources'])==425,'cone membership')
need([n for n in a['candidate_sources'] if a['candidate_sources'][n]!=b['candidate_sources'][n]]==[name], 'unexpected candidate change')
x=dict(a['candidate_sources'][name]);x['source_sha256']=PINS[SOURCE];x['source_bytes']=len(SOURCE.read_bytes())
need(x==b['candidate_sources'][name],'unexpected target row change')
order=b['topological_candidate'];index={n:i for i,n in enumerate(order)}
need(len(order)==len(index)==425 and set(order)==set(b['candidate_sources']) and order[418]==name,'topological candidate')
for n,r in b['candidate_sources'].items():
 for dep in r['source_selected_imports']:
  if dep in index:need(index[dep]<index[n],'dependency order: '+dep+' -> '+n)
affected={name}
while True:
 q=affected|{n for n,r in b['candidate_sources'].items() if affected.intersection(r['source_selected_imports'])}
 if q==affected:break
 affected=q
desc=sorted(affected,key=index.get)
expected=['ZFCinPA.QSchema','ZFCinPA.ValidatorConsistencyLower222','ZFCinPA.ValidatorConsistency222',
 'DiophantineConsistency.HACurrentAssembly2011','DiophantineConsistency.HAExpressionAssembly',
 'DiophantineConsistency.PRAExpressionZFCStrict','DiophantineConsistency.IPRAExpressionNative']
need(desc==expected and order[418:]==expected,'unexpected affected descendants')
failed=json.loads((FAILED/'terminal.json').read_text());passed=json.loads((PASSED/'terminal.json').read_text())
obj=LIB/'ZFCinPA/QSchema.olean'
for where,r,ok in ((FAILED,failed,False),(PASSED,passed,True)):
 need(r['module']==name and r['index']==419 and r['success']==ok and r['exit_code']==(0 if ok else 1),'stage status')
 need(r['source_sha256']==PINS[where/'source.lean'] and r['source_unchanged'] and r['guards_unchanged'],'source/guard receipt')
 need(r['log_sha256']==PINS[where/'compile.log'] and r['lean_sha256']==PINS[LEAN],'stage tool/log')
 need(r['runner_sha256']==sha(where.parents[2]/'run.py'),'stage runner')
 need(not (where/'deps.stderr').read_bytes(),'dependency scan stderr')
 guards={}
 for line in (where/'deps').read_text().splitlines():
  p=Path(line);need(p.is_absolute() and p.suffix=='.olean' and p.is_file(),'bad dependency')
  stem=str(p)[:-len('.olean')]
  for s in SUFFIX:guards[stem+s]=rec(stem+s)
 need(guards==r['guards'] and len(guards)==60,'stage dependency guards')
 need(r['command']==[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={ROOT}/Logic/Interpretability/ZFCinPA/Lean',str(SOURCE),'-o',str(obj)],'stage command')
need(failed['object_sha256'] is None and 'Unknown identifier `InternalInterpretation.consistent_of_falsum_transfer`' in (FAILED/'compile.log').read_text(),'failed diagnostic')
need(passed['object_sha256']==sha(obj)==a['candidate_sources'][name]['object_sha256'],'successful/historical object hash')
need(not (PASSED/'compile.log').read_bytes(),'unexpected successful diagnostics')
for p,h in PINS.items():need(sha(p)==h,'input changed during audit: '+str(p))
for r in (failed,passed):
 need(all(rec(p)==v for p,v in r['guards'].items()),'dependency changed during audit')
print(json.dumps({'status':'PASS','old_source':PINS[FAILED/'source.lean'],'new_source':PINS[SOURCE],
 'old_cone':PINS[OLD],'new_cone':PINS[NEW],'affected_candidate_modules':desc,'failed_exit':1,
 'retry_exit':0,'guard_entries':60,'successful_object_sha256':passed['object_sha256'],
 'successful_object_equals_historical_hash':True,
 'scope':'external source/receipt/guard and selected-source dependency audit; no new Lean replay or package/dynamic ancestry audit'},indent=2,sort_keys=True))
