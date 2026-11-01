from pathlib import Path
import hashlib,json,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');A=Path('/tmp/pra14-full-transitive-7f8okbr0/state.json');D=R/'Computability/DiophantineConsistency/research/pra14_full_source_rebuild_transitive.py';P=Path(__file__).resolve().parent;B=R/'Computability/DiophantineConsistency/reviews/ha87-isolated-full-snapshot/manifest.json';BT=Path('/tmp/ha87-frozen-full-e_jgyudl/tree');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=json.loads(A.read_text());assert a['status']=='AUDIT_PASS';g=a['graph'];prior=json.loads(B.read_text())['source_modules'];anchors={str(p):H(p) for p in [A,B,D,R/'lakefile.toml',R/'lean-toolchain',R/'lake-manifest.json']};root=Path(tempfile.mkdtemp(prefix='pra14-frozen-full-'));tree=root/'tree';tree.mkdir();manifest={};delta={};(P/'source-deltas').mkdir(exist_ok=True)
for n,rel in g['sources'].items():
 src=R/rel;dest=tree/rel;expected=g['source_hashes'][n];assert H(src)==expected,n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);assert H(dest)==expected;old=prior.get(n);manifest[n]={'path':rel,'sha256':expected}
 if old and old['path']==rel and old['sha256']==expected:
  assert H(BT/rel)==expected,n
 else:
  target=P/'source-deltas'/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,target);assert H(target)==expected;delta[n]=rel
for name in ['lakefile.toml','lean-toolchain','lake-manifest.json']:shutil.copyfile(R/name,tree/name);assert H(tree/name)==anchors[str(R/name)]
(tree/'.lake').mkdir();(tree/'.lake/packages').symlink_to((R/'.lake/packages').resolve(),target_is_directory=True)
s=D.read_text().replace("ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')",f"ROOT = Path({str(tree)!r})").replace('Current project sources compiled in dependency order without inherited project objects.','A fixed snapshot of project sources compiled in dependency order without inherited project objects.');assert str(tree) in s
(root/'driver.py').write_text(s);shutil.copyfile(root/'driver.py',P/'driver.py');shutil.copyfile(A,P/'audit-state.json')
for n,row in manifest.items():assert H(R/row['path'])==row['sha256'] and H(tree/row['path'])==row['sha256']
for q,h in anchors.items():assert H(q)==h
m={'root':str(root),'source_modules':manifest,'source_count':len(manifest),'source_delta_modules':delta,'baseline_manifest':str(B),'baseline_manifest_sha256':H(B),'baseline_source_tree':str(BT),'source_audit_state_sha256':H(A),'source_audit_root':str(A.parent),'configuration_sha256':{n:H(tree/n) for n in ['lakefile.toml','lean-toolchain','lake-manifest.json']},'driver_sha256':H(root/'driver.py'),'package_link':str((tree/'.lake/packages').resolve()),'qualification':'Fixed project source snapshot, delta from prior 729-source snapshot; package-transitive ancestry remains inherited. Reused prefix original transitive environment is reconstructed from surviving origin objects.'};(P/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');(root/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(root,'sources',len(manifest),'deltas',len(delta),flush=True)
