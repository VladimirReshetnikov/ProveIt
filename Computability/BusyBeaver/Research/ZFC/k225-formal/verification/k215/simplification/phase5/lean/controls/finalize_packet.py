"""Add read-only review/control receipts and outer telemetry; no archive rewrite."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P/'staged-lean';R=Path('/tmp/k215-proof-phase5')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def copy(src,dst):
 dst=D/dst;assert not dst.exists(),dst;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(Path(src).read_bytes())
raw=json.loads((R/'lean-run1/result.json').read_text()); obs=json.loads((R/'outer-execution-observation.json').read_text())
assert raw['status']=='PASS' and obs['result_sha256']==sha(R/'lean-run1/result.json')
assert obs['outer_session_reported_exit_code']==143
archive=sha(D/'execution.tar.gz'); summary=sha(D/'result.json');before=sha(D/'README.md')
for src,dst in [
(P/'saved-review-run1.json','saved-review.json'),(P/'control-run1.json','controls/actual.json'),
(P/'preflight-controls3.json','controls/preflight.json'),(P/'context-controls1.json','controls/context.json'),
(P/'control.py','controls/control.py'),(P/'preflight_controls.py','controls/preflight_controls.py'),(P/'context_controls.py','controls/context_controls.py'),
(P/'source-freeze-v3.json','controls/source-freeze-v3.json'),
(R/'root-actual-review.json','independent/root-actual-review.json'),(R/'root_readonly_review.py','independent/root_readonly_review.py'),
(R/'outer-execution-observation.json','outer-execution-observation.json'),
(Path('/tmp/k215-proof-phase5-publication-peer/review.json'),'independent/helper-source-peer.json')]:copy(src,dst)
with (D/'README.md').open('a')as f:f.write('''\nThe [saved-reader receipt](saved-review.json) also checks current repository sources. [Actual-record controls](controls/actual.json) reject25 altered records or archives; the earlier metadata-only [preflight](controls/preflight.json) and [context controls](controls/context.json) retain their original scopes. Their exact sources and pre-execution freeze are in `controls/`; they retain historical scratch paths and are separate from the portable saved reader. The independent [root binding review](independent/root-actual-review.json) is preserved with its read-only source.\n\nExecution telemetry is recorded separately in [outer-execution-observation.json](outer-execution-observation.json): the outer tool session reported exit143 after the driver had saved PASS and printed its final completion marker. Its cause is not established, and no successful outer-shell exit is claimed. Every selected compiler and both audits returned0, all required postchecks precede that final marker, and independent post-run reviews rehashed the complete current and predecessor evidence. The outer telemetry does not replace or alter those kernel records.\n''')
assert sha(D/'execution.tar.gz')==archive and sha(D/'result.json')==summary
receipt={'status':'FROZEN_PASS_PACKET_WITH_SEPARATE_OUTER_TELEMETRY','archive_sha256':archive,'summary_sha256':summary,'readme_before_addendum_sha256':before,'readme_after_addendum_sha256':sha(D/'README.md'),'outer_session_reported_exit_code':143,'outer_exit_cause':'unknown','kernel_records_accepted_after_independent_live_and_saved_binding_checks':True,'proof_tools_rerun':False,'historical_helpers_and_archive_unchanged':True,'finalizer_sha256':sha(__file__)}
(D/'publication-finalization.json').write_text(json.dumps(receipt,indent=2)+'\n')
copy(Path(__file__),'controls/finalize_packet.py')
base='Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase5/lean'
files=[{'source':str(f),'destination':base+'/'+f.relative_to(D).as_posix(),'sha256':sha(f),'bytes':f.stat().st_size}for f in sorted(D.rglob('*'))if f.is_file()]
q=P/'copy-map-final.json';assert not q.exists();q.write_text(json.dumps({'status':'FROZEN_COMBINED_PHASE5_PASS','files':files,'file_count':len(files),'bytes':sum(f['bytes']for f in files),'archive_members':733,'scope':'184 complete current closure:37fresh147hash-boundreused,2typedclients10reports; no compiled objects; outer143 retained separately.'},indent=2)+'\n')
print(q,sha(q));print(len(files),sum(f['bytes']for f in files))
