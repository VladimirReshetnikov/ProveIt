#!/usr/bin/env python3
"""Owned offline finite/source audit; no proof-assistant compilation."""
import argparse,hashlib,json,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise SystemExit('Assertions required; do not use -O or -OO.')
P=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('--work',required=True,type=Path);a=ap.parse_args();W=a.work.resolve();assert not W.exists()and P not in W.parents;W.mkdir(parents=True)
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if(P/'MANIFEST.json').exists():
 for n,v in json.loads((P/'MANIFEST.json').read_text()).items():assert H(P/n)==v['sha256']and(P/n).stat().st_size==v['bytes'],n
for d in ['graph_origin','drain_origin','arithmetic','balanced','calculus','runtime']:shutil.copytree(P/d,W/d)
for d,s in [('graph_origin','inspect_trees.py'),('graph_origin','check_ordinal_segments.py'),('drain_origin','contract_drains.py'),('drain_origin','validate_drains.py'),('arithmetic','summarize_arithmetic.py'),('balanced','check_combined.py'),('balanced','test_combined.py'),('calculus','build_proposals.py'),('runtime','check_engine.py'),('runtime','check_tail.py'),('runtime','check_dependencies.py')]:
 subprocess.run([sys.executable,'-B',str(W/d/s)],check=True,stdout=(W/(d+'_'+s+'.log')).open('w'))
assert (W/'graph_origin/ordinal_graph.json').read_bytes()==(P/'drain_origin/input_graph.json').read_bytes()
assert (W/'drain_origin/compact_affine_graph.json').read_bytes()==(P/'arithmetic/input_affine_graph.json').read_bytes()
old=(P/'graph_origin/upstream/KSource215Data.lean').read_text();new=(P/'balanced/inputs/KSource215Data.lean').read_text()
for n in ['t215','tD']:assert old.split('def '+n+' : Tree :=',1)[1].split('\n\n',1)[0]==new.split('def '+n+' : Tree :=',1)[1].split('\n\n',1)[0]
for d,ns in {'arithmetic':['AUDIT.json','arithmetic_core.json','summary_certificates.json','summary_ranks.json'],'balanced':['RESULT.json','balanced_normalized_tree.json','MUTATION_CHECK.json'],'runtime':['DEPENDENCIES.json','ENGINE_FOOTPRINT.json','TAIL_WINDOWS.json']}.items():
 for n in ns:assert json.loads((W/d/n).read_text())==json.loads((P/d/n).read_text()),n
for n in ['KQ1Model.proposed.lean','generate_kq1.proposed.py']:assert (W/'calculus'/n).read_bytes()==(P/'calculus'/n).read_bytes()
for n,h in json.loads((P/'calculus/MANIFEST.json').read_text())['files'].items():assert H(P/'calculus'/n)==h,n
ar=json.loads((W/'arithmetic/AUDIT.json').read_text());br=json.loads((W/'balanced/RESULT.json').read_text());dep=json.loads((W/'runtime/DEPENDENCIES.json').read_text())
r={'status':'LISTED_CHECKS_PASS_WITH_EXPLICIT_BUDGET_LIMITS','kernel_compilation':'NOT PERFORMED','arithmetic':ar,'balanced':br,'dependency_affected':dep['affected'],'dependency_unaffected':dep['unaffected'],'engine':json.loads((W/'runtime/ENGINE_FOOTPRINT.json').read_text()),'calculus':'Owned static generation matches proposed files; received generator not run; Lean not compiled.'}
assert ar['core_edge_regressions_budget_exhausted']==10
(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n');print(r['status'])
