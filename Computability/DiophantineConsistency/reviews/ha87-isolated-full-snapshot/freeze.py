from pathlib import Path
import hashlib,json,os,shutil,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');A=Path('/tmp/ha87-full-transitive-elrmyjhc/state.json');D=R/'Computability/DiophantineConsistency/research/ha87_full_source_rebuild_transitive.py';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
a=json.loads(A.read_text());assert a['status']=='AUDIT_PASS';g=a['graph'];anchors={str(p):H(p) for p in [A,D,R/'lakefile.toml',R/'lean-toolchain',R/'lake-manifest.json']};root=Path(tempfile.mkdtemp(prefix='ha87-frozen-full-'));tree=root/'tree';tree.mkdir();manifest={}
for n,rel in g['sources'].items():
 src=R/rel;dest=tree/rel;expected=g['source_hashes'][n];assert H(src)==expected;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);assert H(dest)==expected;manifest[n]={'path':rel,'sha256':expected}
for name in ['lakefile.toml','lean-toolchain','lake-manifest.json']:shutil.copyfile(R/name,tree/name);assert H(tree/name)==anchors[str(R/name)]
(tree/'.lake').mkdir();(tree/'.lake/packages').symlink_to((R/'.lake/packages').resolve(),target_is_directory=True)
s=D.read_text().replace("ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')",f"ROOT = Path({str(tree)!r})").replace('Current project sources compiled in dependency order without inherited project objects.', 'A fixed snapshot of project sources compiled in dependency order without inherited project objects.');assert str(tree) in s
(root/'driver.py').write_text(s);statehash=H(A)
for n,row in manifest.items():assert H(R/row['path'])==row['sha256'] and H(tree/row['path'])==row['sha256']
for q,h in anchors.items():assert H(q)==h
(root/'manifest.json').write_text(json.dumps({'source_modules':manifest,'source_count':len(manifest),'source_audit_state_sha256':statehash,'source_audit_root':str(A.parent),'configuration_sha256':{n:H(tree/n) for n in ['lakefile.toml','lean-toolchain','lake-manifest.json']},'driver_sha256':H(root/'driver.py'),'package_link':str((tree/'.lake/packages').resolve()),'qualification':'Fixed project source snapshot; transitive package ancestry remains inherited. Reused prefix original environment is reconstructed from surviving origin objects.'},indent=2)+'\n');print(root,'source modules',len(manifest),flush=True)
