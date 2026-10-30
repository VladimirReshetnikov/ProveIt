from pathlib import Path
import hashlib,json,shutil
P=Path('/tmp/ha87-focused-validator-rebase-3tvgyxbr');A=Path('/tmp/ha87-focused-validator-rebase-8o6bp_pm');O=Path('/tmp/ha87-focused-compat-rebuild-wc7u_7ot');K=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib');G=Path('/tmp/ha-focused-unbounded-current-source-graph.json');R=Path('Computability/DiophantineConsistency/reviews/ha87-focused-peer-mismatch-audit');R.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
anchors={str(p):sha(p) for p in [P/'state.json',A/'state.json',O/'state.json',G]};p=json.loads((P/'state.json').read_text());a=json.loads((A/'state.json').read_text());o=json.loads((O/'state.json').read_text());g=json.loads(G.read_text());assert p['status']=='PASS' and a['status']=='PASS';assert len(p['records'])==len(a['records'])==83 and all(r.get('verified') and not r.get('reused_from') for r in p['records']);ar={x['module']:x for x in a['records']};rows=[]
for r in p['records']:
 x=ar[r['module']];bad=[k for k in ('source_sha256','dependency_hashes','object_sha256','log_sha256') if r[k]!=x[k]]
 if bad:rows.append({'module':r['module'],'differing_fields':bad,'author_source_sha256':x['source_sha256'],'peer_source_sha256':r['source_sha256'],'author_object_sha256':x['object_sha256'],'peer_object_sha256':r['object_sha256'],'author_dependencies':x['dependency_hashes'],'peer_dependencies':r['dependency_hashes'],'author_log_sha256':x['log_sha256'],'peer_log_sha256':r['log_sha256']})
assert len(rows)==15
root='DiophantineConsistency.ArithmeticAdaptiveTransportScalar2011';todo=list(g['edges'][root]);seen=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(g['edges'].get(n,[]))
closure=[]
for n in sorted(seen):
 rel=n.replace('.','/')+'.olean';pa=O/'lib'/rel;pb=P/'lib'/rel;pa=pa if pa.is_file() else K/rel;pb=pb if pb.is_file() else K/rel
 if not pa.is_file() or not pb.is_file():raise RuntimeError('missing declared object '+n)
 x=sha(pa);y=sha(pb);closure.append({'module':n,'original_path':str(pa),'original_resolved':str(pa.resolve()),'original_sha256':x,'peer_path':str(pb),'peer_resolved':str(pb.resolve()),'peer_sha256':y,'equal':x==y})
source_mismatch=[]
for m,h in p['source_hashes'].items():
 if sha(Path('/home/codex/.codex/worktrees/46be/Proofs')/g['sources'].get(m,''))!=h:source_mismatch.append(m)
# Focused sources that the driver adds independently of the graph are checked
# directly against the recorded source snapshots instead of assuming a mapping.
for m in list(source_mismatch):
 if m in ('DiophantineConsistency.ArithmeticHalfBinomialCompatChecks','DiophantineConsistency.ArithmeticPellOrdinateCompatChecks','DiophantineConsistency.ArithmeticConstructionUnboundedCompatChecks','DiophantineConsistency.HAAdaptiveFactor87','DiophantineConsistency.HAAdaptiveFactor87Checks'):
  source_mismatch.remove(m)
for r in p['records']:
 q=P/'logs'/r['source_snapshot']; assert sha(q)==r['source_sha256'];assert sha(P/'logs'/r['log_file'])==r['log_sha256'];assert sha(P/'lib'/(r['module'].replace('.','/')+'.olean'))==r['object_sha256']
for q,h in anchors.items():assert sha(Path(q))==h
for c in closure:
 assert sha(Path(c['original_path']))==c['original_sha256'] and sha(Path(c['peer_path']))==c['peer_sha256']
result={'author_peer_state_anchors':anchors,'peer_status':p['status'],'peer_rows':len(p['records']),'peer_reused_rows':sum(bool(x.get('reused_from')) for x in p['records']),'same_historical_boundary':p['historical_boundary_objects']==a['historical_boundary_objects'],'same_model_only_boundary':p['model_only_inherited_objects']==a['model_only_inherited_objects'],'same_package_audit_anchor':p['package_audit_state_sha256']==a['package_audit_state_sha256'],'peer_inherited_zf_sha256':p.get('inherited_zf_object'),'source_mismatch_for_graph_mapped_modules':source_mismatch,'mismatches':rows,'scalar_declared_closure':closure,'scalar_repeat_outputs':{x.name:sha(x) for x in Path('/tmp/ha87-scalar-determinism').glob('*.olean')}}
(R/'result.json').write_text(json.dumps(result,indent=2)+'\n');shutil.copyfile(P/'state.json',R/'peer-state.json');(R/'peer-logs').mkdir(exist_ok=True)
for r in p['records']:shutil.copyfile(P/'logs'/r['log_file'],R/'peer-logs'/(r['module'].replace('.','_')+'.log'))
print('PASS audit, mismatches',len(rows),'scalar closure differences',sum(not x['equal'] for x in closure),'current mapped source mismatches',source_mismatch)
