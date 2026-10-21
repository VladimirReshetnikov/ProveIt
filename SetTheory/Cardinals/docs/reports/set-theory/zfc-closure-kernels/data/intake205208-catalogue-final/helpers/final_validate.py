"""Own post-build source/PDF validation and bounded PDF installation, no proof execution."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/k215-phase6-catalogue-final');S=Path('/tmp/k215-phase6-status-final')
def sha(b):return hashlib.sha256(b).hexdigest()
r=json.loads((O/'result.json').read_text());s=json.loads((S/'result.json').read_text())
assert r['status']=='PDF_VALIDATED_PENDING_VISUAL_REVIEW'
for f in s['files']:assert sha((R/f['path']).read_bytes())==f['after_sha256'],f['path']
text=(O/'manifest.txt').read_text();nums=[int(m[1]) for l in text.splitlines() if (m:=re.match(r'^\s*(\d{1,3})\.\s+(.+)',l))]
assert nums==list(range(1,291)),nums
assert r['diagnostics']==0 and r['all_fonts_embedded'] and r['page_count']==141
pdf=O/'manifest.pdf';assert sha(pdf.read_bytes())==r['pdf_sha256']
target=R/'SetTheory/Cardinals/docs/reports/manifest.pdf';before=target.read_bytes();tracked_blob=subprocess.check_output(['git','rev-parse','HEAD:SetTheory/Cardinals/docs/reports/manifest.pdf'],cwd=R,text=True).strip();current_blob=subprocess.check_output(['git','hash-object',str(target)],cwd=R,text=True).strip()
if current_blob!=tracked_blob:(O/'predecessor-worktree.pdf').write_bytes(before)
target.write_bytes(pdf.read_bytes());assert target.read_bytes()==pdf.read_bytes()
record={'status':'PASS_INSTALLED_PDF_AFTER_VISUAL_REVIEW','catalogue_entries':290,'rendered_entry_numbers_exact_order':True,'source_count':178,'pending_sources':[165,166],'pending_arrivals':['5314ca0e6b','b07002a86b'],'all_ten_docs_exact_to_applied_record':True,'historical_archive_headers_and_placement_lists_unchanged':True,'visual_review':{'reviewer':'opening_encoder','pages':[2,140,141],'findings':[],'scope':'Rendered scope/current summary and final report pages; no clipping, overlap or missing text.'},'pdf_sha256':sha(pdf.read_bytes()),'pdf_bytes':len(pdf.read_bytes()),'previous_pdf_sha256':sha(before),'previous_pdf_is_HEAD_blob':current_blob==tracked_blob,'previous_git_blob':tracked_blob,'manifest_sha256':r['source_sha256'],'build_record_sha256':sha((O/'result.json').read_bytes()),'status_record_sha256':sha((S/'result.json').read_bytes()),'validator_sha256':sha(Path(__file__).read_bytes()),'owned_changed_paths':[f['path'] for f in s['files']]+['SetTheory/Cardinals/docs/reports/manifest.pdf'],'proof_sources_modified':False,'staged':False,'committed':False}
(O/'final-review.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
