#!/usr/bin/env python3
"""Owned offline release replay. Executes only the explicitly listed owned scripts."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, shutil, subprocess, sys
if not __debug__: raise SystemExit('Assertions must be enabled')
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--work',required=True,type=Path);a=ap.parse_args();W=a.work.resolve()
assert not W.exists() and P not in W.parents,'Use a fresh directory outside the packet'
H=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((P/'MANIFEST.json').read_text())
actual={p.relative_to(P).as_posix()for p in P.rglob('*')if p.is_file()}
assert actual==set(m)|{'MANIFEST.json'},'Unlisted or missing package file'
for n,r in m.items():
    q=PurePosixPath(n)
    assert not q.is_absolute() and '..' not in q.parts and '\\' not in n
    p=P/n;assert not p.is_symlink() and p.is_file(),n
    b=p.read_bytes();assert H(b)==r['sha256'] and len(b)==r['bytes'],n
W.mkdir(parents=True)
for d in ['review','calculus','structural','runtime']:shutil.copytree(P/d,W/d)
commands=[('review','replay_bytes.py'),('review','replay_delta.py'),('calculus','audit_proposal.py'),('structural','build_proposals.py'),('runtime','check_framed_templates.py'),('runtime','discover_left_frames.py'),('runtime','test_negative_mutations.py'),('runtime','check_label_mapping.py')]
for d,f in commands:
    with(W/(d+'_'+f+'.log')).open('w')as log:
        # Do not use -I here: the three runtime diagnostics import their owned sibling helper.
        subprocess.run([sys.executable,'-B',str(W/d/f)],cwd=W,stdout=log,stderr=subprocess.STDOUT,check=True)
products={
'review':['OWNED_REPLAY.json','DELTA_REPLAY.json'],
'calculus':['AUDIT.json','PROPOSAL_METRICS.json','local_equality_capabilities.patch','proposed/TarskiDerived.lean','proposed/TarskiLeibniz.lean','proposed/KThmK.lean'],
'structural':['AUDIT.json','SHARED_STACK.patch','ROCQ_STEP_SOUND.patch','proposed/EnumStack.lean','proposed/EnumDom.lean','proposed/EnumPerm.lean','proposed/L1_SoundPerm.v','proposed/producer_L1_SoundPerm.v'],
'runtime':['FRAMED_TEMPLATES.json','LEFT_FRAME_DISCOVERY.json','BOUNDARY_TESTS.json','LABEL_MAPPING.json','FORMAL_TEMPLATES.json']}
for d,names in products.items():
    for n in names:assert(W/d/n).read_bytes()==(P/d/n).read_bytes(),f'Replay drift: {d}/{n}'
base=P/'review/current/Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
prior_map={r['current'].split('/Proofs/')[1]:r['sha256']for r in json.loads((P/'review/prior_current_review.json').read_text())['sources'].values()}
for n in ['TarskiDerived.lean','TarskiLeibniz.lean','KThmK.lean']:
    assert(P/'calculus/inputs'/n).read_bytes()==(base/n).read_bytes(),n
for n,r in json.loads((P/'runtime/reference/PINS.json').read_text()).items():
    b=(P/'runtime/reference'/n).read_bytes();assert H(b)==r['sha256'] and len(b)==r['bytes'],n
for n in ['KRuntimeCore.lean','KHome.lean','KHomeReady.lean','KSim.lean','KDecoderPrefix215.lean']:
    b=(P/'runtime/reference'/n).read_bytes()
    assert b==(base/n).read_bytes() and H(b)==prior_map['Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+n],n
r=json.loads((W/'runtime/LEFT_FRAME_DISCOVERY.json').read_text())
assert(r['templates'],r['framed_guard_uses'],r['literal_control_guards'],r['total_expensive_obligations'])==(35,1422,3,4789)
result={'status':'PASS_OWNED_OFFLINE_REPLAY','manifest_files':len(m),'owned_scripts_run':len(commands),'current_sources_bound':198,'prior_sources_bound':199,'accepted_scope_delta_lines':-653,'accepted_scope_delta_bytes':-36327,'runtime_templates':35,'runtime_templated_guards':1422,'runtime_candidate_expensive_obligations':4789,'all_source_coverage_instances_still_required':6176,'structural_lean_production_delta_lines':-39,'rocq_unique_proof_delta_lines':-9,'rocq_synchronized_tree_delta_lines':-18,'calculus_production_delta_lines':-5,'kernel_compilation':'NOT PERFORMED','limits':'Data integrity, owned textual transformations and finite symbolic diagnostics only. No new universal theorem, endpoint rebuild or measured speedup.'}
(W/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
