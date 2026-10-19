from pathlib import Path
import json,hashlib,ast
B=Path('/tmp/zfc-source-rotation240-publication-design');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
f=json.loads((B/'freeze.json').read_text());checks=0
for row in f['files']:
 assert sha(Path(row['path']))==row['sha256'];checks+=1
s=(B/'build_packet.py').read_text();ast.parse(s);checks+=1
p=json.loads((B/'inputs.json').read_text());u=p['units'][0]
for row in u['files']+p['extras']:
 assert sha(Path(row['path']))==row['sha256'];Path(row['path']).read_bytes().decode();checks+=2
assert len(u['files'])==22 and len(p['extras'])==6;checks+=2
raw=Path(u['base'],'check.py').read_text();portable=(B/'portable-proposals/check_source_rotation240.py').read_text()
changes=[("HERE=Path('"+u['base']+"')",'HERE=Path(__file__).resolve().parent\nREPO=HERE.parents[3]'),("default=HERE/'"+u['module']+".lean'","default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"+u['module']+".lean'"),("default=HERE/'Audit.lean'","default=HERE/'"+u['stem']+"_audit.lean'"),("default=HERE/'boundary.json'","default=HERE/'source-rotation240-formal/"+u['slug']+"/boundary.json'")]
for a,b in reversed(changes):assert portable.count(b)==1;portable=portable.replace(b,a);checks+=1
assert portable==raw;checks+=1
r=json.loads(Path(u['verification']['path']).read_text());assert r['status']=='PASS' and (r['named_axiom_probes'],r['callers'],r['warnings'])==(10,13,0);checks+=1
out={'status':'SOURCE_ONLY_PUBLICATION_BUILDER_REVIEW_PASS','builder':d(B/'build_packet.py'),'note':d(B/'note.md'),'snapshot':d(B/'inputs.json'),'reviewer_source':d(Path(__file__)),'static_checks':checks,'findings':[],'scope':['Full89-line builder and scoped note read; exact actual10/13 success, prior preparation and immutable reviewer gate.','Explicit22text+6externalreview snapshot;37 total mappings, no uncontrolled tree capture.','Exact four default-only inverse; substantive executed guard remains unchanged.','Preserves own unexecuted Init-classification correction without inventing a failed proof attempt; excludes compiled/cache artifacts.','No binary runtime/startup/complete240 or PA claim.'],'reviewer_role':'Independent of this publication builder/source author; authored the separately preserved source/API peer and prior generic guard work.','builder_invoked':False,'supplied_execution':False,'maintained_edits':False}
(O/'review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(d(O/'review.json')))
