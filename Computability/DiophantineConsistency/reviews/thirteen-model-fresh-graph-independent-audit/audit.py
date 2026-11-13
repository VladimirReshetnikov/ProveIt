#!/usr/bin/env python3
"""Independent read-only artifact audit of the joined 2011-to-69 pair."""
import hashlib, importlib.util, json, re, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/thirteen-model-fresh-graph'
OUT=Path('/tmp/ipra-thirteen-fresh-graph-pair-01')
VIEW=Path('/tmp/ipra-thirteen-model-view-pair-01')
FRESH=Path('/tmp/ipra-thirteen-fresh-private-pair-01')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
RECEIPT='45fe986c010157516b76c665e36106726fe9a44349406e2665890ba6ad9c2996'
SOURCE='815d0304371e78aa4916d657a8e26857ae0faeefab74a524c5a56197c5c966d8'
OBJECT='d943146640b461d4ce6587fdd77f0552414a93d60cac55958b3b35bc72106753'
EXPECTED={'ArithmeticOddOrdinateResidue.olean','ArithmeticPellAuxiliarySeed.olean','ArithmeticPellPigeonhole.olean','ArithmeticPellSquaredSeed.olean','DiscreteOrderedRingFacts.olean','ModelArithmetic.olean','ModelBAuxiliary.olean','ModelBFreshPrivate.olean','ModelBNegativeResidue.olean','ModelBPositiveCarrier.olean','ModelBSeed.olean'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def main():
    names=('README.md','Model69FreshNorms.lean','failed-audit-exit-key.py','failed-fixed-tuple-kernel-memory.lean','failed-fresh-readme-audit.py','failed-highport-cast.lean','failed-positive-helper-parser.lean','warning-unused-section.lean','replay.py','replay-receipt.json','terminal-observation.json')
    for name in names:
        p=PKG/name;b=subprocess.run(['git','show','ca2b5071e3:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed bytes '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes())
    need(obs['session']==61621 and obs['actual_exit_code']==0 and obs['receipt_sha256']==RECEIPT and obs['stdout']=='PASS_PAIRED_THIRTEEN_FRESH_GRAPH '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT,'receipt')
    r=json.loads((PKG/'replay-receipt.json').read_bytes())
    need(r['status']=='PASS_PAIRED_THIRTEEN_FRESH_GRAPH' and len(r['runs'])==2 and len(r['parent_audits'])==4,'status')
    spec=importlib.util.spec_from_file_location('pinned_replay',PKG/'replay.py'); replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay)
    replay.check_pins();parents=replay.verify_audits();need(parents==r['parent_audits'],'independent reruns of four parent audits')
    summaries=[]; reports=['fresh_ring_norms','graph_zero_of_fresh','current_view_fields','current_positive_graph_zero','current_shifted_zero_of_port_binding','current_port_binding','current_shifted_zero']
    for row,side in zip(r['runs'],('author','peer')):
        run=OUT/side;src=run/'src/Model69FreshNorms.lean';obj=run/'Model69FreshNorms.olean';lib=run/'lib';view=VIEW/side/'lib';fresh=FRESH/side/'lib/DiophantineConsistency'
        need(row['label']==side and row['exit']==row['deps_exit']==0 and not row['stderr'],'recorded exits')
        need(sha(src)==sha(PKG/'Model69FreshNorms.lean')==row['source_sha256']==SOURCE and sha(obj)==row['object_sha256']==OBJECT,'source/object')
        need(row['command'][1:4]==['-M4000','-j1','-DElab.async=false'] and row['command'][-1]==str(obj),'compiler command')
        vf={p.relative_to(view) for p in view.rglob('*.olean')};lf={p.relative_to(lib) for p in lib.rglob('*.olean')}
        freshfiles={p.name for p in fresh.glob('*.olean')}; viewfiles={p.name for p in (view/'DiophantineConsistency').glob('*.olean')}
        matched=freshfiles&viewfiles;added=freshfiles-viewfiles
        need(len(matched)==65 and added==EXPECTED and set(row['matched_project_objects'])==matched and set(row['added_fresh_objects'])==added,'overlap inventory')
        need(lf==vf|{Path('DiophantineConsistency')/n for n in added},'joined inventory')
        for rel in vf:need((lib/rel).resolve()==(view/rel).resolve() and sha(lib/rel)==sha(view/rel),'view object '+str(rel))
        for name in matched:need(sha(fresh/name)==sha(view/'DiophantineConsistency'/name)==sha(lib/'DiophantineConsistency'/name)==row['matched_project_objects'][name],'matched '+name)
        for name in added:
            q=lib/'DiophantineConsistency'/name;need(q.is_symlink() and q.resolve()==(fresh/name).resolve() and sha(q)==row['added_fresh_objects'][name],'added '+name)
        deps={str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ModelBFreshPrivate.olean'),str(lib/'DiophantineConsistency/Thirteen69Cuts.olean'),str(Path('/tmp/ipra-thirteen-retained-norm-pair-01')/side/'Model69RetainedNorm.olean'),str(Path('/tmp/ipra-thirteen-current-outer-pair-01')/side/'Model69CurrentOuter.olean'),str(Path('/tmp/ipra-thirteen-current-phase-pair-01')/side/'Model69CurrentPhase.olean')}
        need(set(row['deps_stdout'].splitlines())==deps and all(Path(x).is_file() for x in deps),'direct dependencies')
        found=re.findall(r"^'Model69FreshNorms\.([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M)
        need([n for n,_ in found]==reports and [a for _,a in found]==['propext, Classical.choice, Quot.sound']*7 and row['axiom_reports']==[a for _,a in found] and not re.search(r'warning:|error:|sorryAx|\bsorry\b',row['stdout']),'reports')
        summaries.append({'side':side,'source_sha256':SOURCE,'object_sha256':OBJECT,'matched_fresh_objects':len(matched),'added_fresh_objects':len(added),'recorded_compiler_exit':0,'recorded_deps_exit':0,'axiom_reports':7})
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_FRESH_GRAPH_AUDIT','source_commit':'ca2b5071e3','author_receipt_sha256':RECEIPT,'recorded_outer_session':61621,'recorded_outer_exit':0,'parent_audit_rerun_exits':[0,0,0,0],'runs':summaries,'scope':'Conditional actual positive current-2011 zero yields shifted 69-node literal zero with four explicit model-port equalities; no unconditional converse, full axiom inventory, iPRA proof or package-transitive/dynamic provenance claim.'},indent=2))
if __name__=='__main__':main()
