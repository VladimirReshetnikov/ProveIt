#!/usr/bin/env python3
"""Pins, independent combinatorics, optional bounded replay; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-88-local-rewrite-screen'
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
final_readme=read(A/'README.md','911422dbed5ff3f41af818c045872fbf10a5777ce72ba883a7d8a9dbf6f31454')
link_tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-88-local-rewrite-screen-independent/`.\n'
assert final_readme.endswith(link_tail)
previous=final_readme[:-len(link_tail)]
needle=b'This packet does not cover arbitrary integer leaves'
assert previous.count(needle)==1
previous=previous.replace(needle,b'This packet has not received a separate independent review. It does not cover arbitrary integer leaves',1)
assert hashlib.sha256(previous).hexdigest()=='ad944f5a09f192e38f716f3a60f2bff76e4fe521ce84da5c02fe2a6245a573a1'
read(A/'local.py','b382d3e720ad9496995870ed0ba3deebf80e562955b91e51414d1e322cf79133');read(A/'beam.py','64f80fc32ebe3d6f11ea9ffef33766b3db985ee0b16c635237a2cf473b6731a3')
local=json.loads(read(A/'local-result.json','c01ae952410ab1f1b7a40d2597cc2f0432cf121b93aaead1b3a1ef75f857f8dd'));beam=read(A/'beam-result.txt','a3244a790e3c29319923319458354b0d95beeba506bb2a6824975ec73118dafd')
g=json.loads(read(D/'research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'));assert len(g['source'])==88 and len(g['witnesses'])+len(g['fixed_numerals'])==17
assert sum(2*n*n+n for n in range(22,110))==874412 and sum(4*n-1 for n in range(22,110))==22968
for key in ('uniform','fixed'):
 x=local[key];assert x['original_live']==88 and not x['one_gate_candidates'] and not x['two_gate_candidates'];assert x['counts']['targets']==88 and x['counts']['first_gates']==874412 and x['counts']['second_queries']==22968 and x['counts']['targets_with_sample_zero']==0 and x['counts']['sample_zero_nonconstant']==0
assert local['alias_sign']=={'aliases':[],'square_only_negations':[]} and local['control']['aliases'] and beam.splitlines()[-1]==b'DONE 88' and len(beam.splitlines())==11
# Basic reassembly/factoring identities on an exhaustive small box.
for a in range(-4,5):
 for b in range(-4,5):
  for c in range(-4,5):
   assert (a+b)+c==a+(b+c) and (a-b)+c==a-(b-c) and a*(b+c)==a*b+a*c and a*b+a*c==a*(b+c)
if sys.argv[1:]==['--replay']:
 for script,out,limit in [('local.py','local-result.json',120),('beam.py','beam-result.txt',180)]:
  r=subprocess.run([sys.executable,'-I','-S','-B',str(A/script)],capture_output=True,check=True,timeout=limit);assert r.stdout==(A/out).read_bytes()
elif sys.argv[1:]:raise SystemExit('usage: check.py [--replay]')
print(json.dumps({'independent_first_gate_count':874412,'independent_second_query_count':22968,'beam_final_live':88,'uniform_only_alias_sign':True,'scope':'bounded exact-target modular and pruned structural search; no global lower bound or Lean'},sort_keys=True,indent=2))
