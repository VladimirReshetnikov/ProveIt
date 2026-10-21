"""Own selected leaf driver; deliberately does not invoke verify.main/manifests."""
from pathlib import Path
import sys,json,importlib.util,time
P=Path(__file__).resolve().parent;R=P/'packet';sys.path[:0]=[str(R/'code')]
import verify
spec=importlib.util.spec_from_file_location('dense',R/'experiments/machine_compression/check_blank_endpoints_dense.py');dense=importlib.util.module_from_spec(spec);spec.loader.exec_module(dense)
start=time.monotonic()
a={'status':'PASS','source_edits':verify.source_edits(),'delivered_receipt_audits':[verify.audit(n)for n in ('omit-zero','dmn')],'fresh_startups':[dense.verify(dense.SPECS[i],R/'experiments/machine_compression'/dense.SPECS[i]['file'])for i in (1,2)],'scope':'Exact source and ordered delivered receipt audits plus fresh two new finite blank endpoints. No manifest, ancestor startup, prototype search, or proof assistant.'}
a['seconds']=time.monotonic()-start;(P/'selected-audit.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps({'status':a['status'],'seconds':a['seconds'],'runtime_case_counts':[x['guards']for x in a['delivered_receipt_audits']],'startup_steps':[x['steps']for x in a['fresh_startups']]}))
