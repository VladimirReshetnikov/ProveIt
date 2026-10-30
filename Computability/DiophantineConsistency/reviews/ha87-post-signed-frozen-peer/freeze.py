from pathlib import Path
import hashlib,json,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');A=Path('/tmp/ha87-focused-validator-rebase-z7kphtk1');G=Path('/tmp/ha-focused-post-scaled-source-graph.json');P=Path('/tmp/ha-preserved-model-rebuild-plan.json');D=Path('/tmp/ha87-focused-post-scaled-rebase.py'); H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
state=json.loads((A/'state.json').read_text());graph=json.loads(G.read_text());sources=dict(graph['sources'])
for name in ['ArithmeticHalfBinomialCompatChecks','ArithmeticPellOrdinateCompatChecks','ArithmeticConstructionUnboundedCompatChecks','HAAdaptiveFactor87','HAAdaptiveFactor87Checks']:
 sources['DiophantineConsistency.'+name]='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name+'.lean'
root=Path(tempfile.mkdtemp(prefix='ha87-frozen-peer-'));tree=root/'tree';tree.mkdir();seen={};manifest={}
for key,folder in [('current_ha_source_hashes','current-ha-source-snapshots'),('source_hashes','source-snapshots')]:
 for m,h in state[key].items():
  src=A/folder/(m.replace('.','_')+'.lean');dest=tree/sources[m];assert H(src)==h
  if dest in seen:
   assert seen[dest]==h
  else:
   dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);assert H(dest)==h;seen[dest]=h
  manifest[m]={'path':sources[m],'sha256':h}
zf=R/'.lake/build/lib/lean/ZF/Zf.olean';assert H(zf)=='7dd1c71a91dcd57ffb9c0d5a2256a92140a5e6efb6a8f6f939edd285bf5a7eae';zf_dst=tree/'.lake/build/lib/lean/ZF/Zf.olean';zf_dst.parent.mkdir(parents=True,exist_ok=True);zf_dst.symlink_to(zf.resolve());shutil.copyfile(G,root/'graph.json');shutil.copyfile(P,root/'overlap-plan.json');assert H(root/'graph.json')==H(G) and H(root/'overlap-plan.json')==H(P)
s=D.read_text().replace("R=Path('/home/codex/.codex/worktrees/46be/Proofs')",f"R=Path({str(tree)!r})").replace("graph=Path('/tmp/ha-focused-post-scaled-source-graph.json')",f"graph=Path({str(root/'graph.json')!r})").replace("plan=Path('/tmp/ha-preserved-model-rebuild-plan.json')",f"plan=Path({str(root/'overlap-plan.json')!r})").replace("cmd=['lean','-M8000'", "cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M8000'")
assert str(tree) in s and str(root/'graph.json') in s and str(root/'overlap-plan.json') in s and "cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'" in s
(root/'driver.py').write_text(s);(root/'manifest.json').write_text(json.dumps({'source_modules':manifest,'unique_source_files':len(seen),'historical_zf_sha256':H(zf),'graph_sha256':H(G),'plan_sha256':H(P),'driver_sha256':H(root/'driver.py'),'author_state_at_freeze':H(A/'state.json'),'qualification':'Source snapshots are isolated; HA/ZF/Foundation and external-package provider ancestry remains inherited.'},indent=2)+'\n');print(root, 'modules',len(manifest),'unique_sources',len(seen),flush=True)
