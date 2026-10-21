#!/usr/bin/env python3
"""Owned independent replay; not a Lean/Rocq kernel build."""
import argparse,hashlib,json,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise SystemExit('Assertions required; do not use -O or -OO.')
P=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);a=ap.parse_args();W=a.work.resolve();assert not W.exists()and P not in W.parents;W.mkdir(parents=True)
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if(P/'MANIFEST.json').exists():
 for n,v in json.loads((P/'MANIFEST.json').read_text()).items():assert H(P/n)==v['sha256']and(P/n).stat().st_size==v['bytes'],n
for d in ['graph_origin','structural','runtime']:shutil.copytree(P/d,W/d)
old=(P/'graph_origin/upstream/KSource215Data.lean').read_text();new=(P/'review/KSource215Data.lean').read_text()
for n in ['t215','tD']:assert old.split('def '+n+' : Tree :=',1)[1].split('\n\n',1)[0]==new.split('def '+n+' : Tree :=',1)[1].split('\n\n',1)[0]
for d,s in [('graph_origin','inspect_trees.py'),('graph_origin','check_ordinal_segments.py'),('structural','minimize_graph.py'),('structural','interval_invariants.py'),('structural','contract_drains.py'),('structural','validate_drains.py'),('runtime','check_patch.py'),('runtime','test_patch.py'),('runtime','check_decoder.py'),('runtime','check_dr_delta.py')]:
 subprocess.run([sys.executable,'-B',str(W/d/s)],check=True,stdout=(W/(d+'_'+s+'.log')).open('w'))
assert (W/'graph_origin/ordinal_graph.json').read_bytes()==(P/'structural/input_graph.json').read_bytes()
checks={'structural':['DRAIN_AUDIT.json','ADVERSARIAL_AUDIT.json','QUOTIENT_AUDIT.json','INTERVAL_AUDIT.json','compact_affine_graph.json','affine_graph.json','drain_ranks.json','drain_certificates.json'],'runtime':['PATCH_RESULT.json','DR_DELTA.json']}
for d,ns in checks.items():
 for n in ns:assert json.loads((W/d/n).read_text())==json.loads((P/d/n).read_text()),n
for n,h in json.loads((P/'calculus/MANIFEST.json').read_text())['files'].items():assert H(P/'calculus'/n)==h,n
s=(P/'calculus/KSeedModel222.proposed.lean').read_text();assert all('theorem '+n not in s for n in ['enc_pos','enc_dec_enc','eqFree_dec_enc']);assert 'le_P_right' in s and 'sat_encode_decode' in s
r={'status':'LISTED_INDEPENDENT_CHECKS_PASS','kernel_compilation':'NOT PERFORMED','graph_regenerated':True,'current_tree_alignment':True,'drains':json.loads((W/'structural/DRAIN_AUDIT.json').read_text()),'patch':json.loads((W/'runtime/PATCH_RESULT.json').read_text()),'dr_affected_guards':json.loads((W/'runtime/DR_DELTA.json').read_text())['affected_guard_count'],'calculus':'File pins and three removed induction names checked; proposed Lean not compiled.'}
(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
