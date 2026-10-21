#!/usr/bin/env python3
"""Replay owned finite-data audits; does not invoke a proof-assistant kernel."""
import argparse,hashlib,json,shutil,subprocess,sys,re
from pathlib import Path
if not __debug__:raise SystemExit('Assertions required; do not use -O or -OO.')
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--work',required=True,type=Path);a=ap.parse_args();W=a.work.resolve();assert not W.exists() and P not in W.parents;W.mkdir(parents=True)
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if(P/'MANIFEST.json').exists():
 for n,v in json.loads((P/'MANIFEST.json').read_text()).items():assert H(P/n)==v['sha256'] and(P/n).stat().st_size==v['bytes'],n
old=(P/'structural/upstream/KSource215Data.lean').read_text();new=(P/'current_upstream/KSource215Data.lean').read_text()
for name in ['p215Nodes','p215','t215','tD']+[f'fwd{i}'for i in range(16)]+['fwdCert']:
 def declaration(s):
  start=re.search(r'(?m)^def '+name+r'\b',s).start();return s[start:].split('\n\n',1)[0]
 assert declaration(old)==declaration(new),name
assert (P/'calculus/upstream/KSeedModel222.lean').read_text().rstrip('\n')==(P/'current_upstream/KSeedModel222.lean').read_text().rstrip('\n')
for d in ['structural','startup','runtime']:shutil.copytree(P/d,W/d)
for part,script in [('structural','inspect_trees.py'),('structural','check_ordinal_segments.py'),('startup','audit_startup.py')]:
 subprocess.run([sys.executable,'-B',str(W/part/script)],check=True,stdout=(W/(script+'.log')).open('w'))
for part,files in [('structural',['trees.json','leaves.json','ordinal_graph.json','ORDINAL_GRAPH_AUDIT.json','CanonicalCert215.lean']),('startup',['RESULT.json','sweep_certificate.json'])]:
 for n in files:assert (W/part/n).read_bytes()==(P/part/n).read_bytes(),n
r=subprocess.run([sys.executable,'-B',str(W/'runtime/check_decoder.py')],check=True,capture_output=True,text=True)
(W/'decoder.jsonl').write_text(r.stdout)
decoder=[json.loads(line) for line in r.stdout.splitlines()]
assert [x['templates'] for x in decoder]==[281,281,281,282]
assert [x['edges'] for x in decoder]==[468,468,470,472]
subprocess.run([sys.executable,'-B',str(P/'current_upstream/check_formal_binding.py')],check=True,stdout=(W/'formal_binding.log').open('w'))
subprocess.run([sys.executable,'-B',str(W/'runtime/check_formal_alignment.py')],check=True,stdout=(W/'formal_alignment.log').open('w'))
assert json.loads((W/'runtime/FORMAL_ALIGNMENT.json').read_text())==json.loads((P/'runtime/FORMAL_ALIGNMENT.json').read_text())
subprocess.run([sys.executable,'-B',str(W/'runtime/test_rejection.py')],check=True,stdout=(W/'decoder_rejection.log').open('w'))
assert (P/'current_upstream/k215.native.tm').read_bytes()==(P/'runtime/inputs/K215_Formal.tm').read_bytes()
leaves=json.loads((W/'structural/leaves.json').read_text())['source'];ops={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}
expected=[[path,ops[e[0]],e[1]if len(e)>1 else None]for path,e in leaves]
assert expected==json.loads((P/'runtime/inputs/K215_Formal.sites.json').read_text())
m=json.loads((P/'calculus/MANIFEST.json').read_text())
for n,h in m['files'].items():assert H(P/'calculus'/n)==h,n
src=(P/'calculus/upstream/KSeedModel222.lean').read_text();dst=(P/'calculus/KSeedModel222.proposed.lean').read_text()
assert 'theorem enc_dec_enc' in src and 'theorem eqFree_dec_enc' in src
assert 'theorem enc_dec_enc' not in dst and 'theorem eqFree_dec_enc' not in dst
assert 'sat_encode_decode' in dst and 'derivable_named_bundle' in dst
out={'status':'LISTED_INDEPENDENT_DATA_CHECKS_PASS','kernel_compilation':'NOT PERFORMED','decoder_products':decoder,'structural_graph':json.loads((W/'structural/ORDINAL_GRAPH_AUDIT.json').read_text()),'startup':json.loads((W/'startup/RESULT.json').read_text()),'calculus':'Pinned files and named dependency deletion checked; proposed Lean not compiled.'}
(W/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
