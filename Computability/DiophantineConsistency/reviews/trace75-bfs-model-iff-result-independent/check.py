from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-bfs-model-iff-prototype'; a=h/'observations/modeliff-attempt02';o=h/'observations/outer-attempt02';t=json.loads((a/'terminal.json').read_text());outer=json.loads((o/'result.json').read_text());obj=Path(t['output_root'])/'Trace75BFSModelIff.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='c2b163694d1617aee0e499abd72355740e5fcc0579c5ae5e20df57ab686f7f6b' and sha(o/'result.json')=='7d42a1efe1029ce3b2145f7f6b69df0f6bf737146168fb3fa986fdccdccb3af3'
assert t['exit']==0 and t['reason'] is None and t['pins']==t['after'] and t['direct_imports']==t['direct_imports_after']
assert outer['child_exit']==0 and outer['terminal_sha256']==sha(a/'terminal.json') and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_before']==outer['wrapper_after']==sha(h/'run-outer-v3.py')=='a9863903a204a9223e8168427a23fe4d6710b2d20c653a519bcf5a192b22fb1d'
for p,d in outer['inputs_before'].items():assert sha(p)==d
for n in ('stdout','stderr'):assert sha(o/n)==outer[n+'_sha256'] and sha(a/n)==t[n+'_sha256']
src=h/'Trace75BFSModelIff.lean';assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['pins']['source']=='056683d3dc060692817d8af6d40800417d5c6f254dfa9333577527641e7a388c'
assert sha(h/'run-v3.py')==t['pins']['runner']=='abf2711130afe21e3f5a679f8a6275eb514cce98d0c70ae7a27806eebbb4db4e'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='e97639a427341e14bea30db3fed307556bedff7e9dfa50c6710f89f5bbe5c863'
assert (a/'stdout').read_text()=="'Trace75BFSModelIff.positive_model_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
mods=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M);assert mods==['Trace75BFSHaltGraph','Trace75BFSModelHalt','CompactSymbolicBetaCast','CompactSymbolicMaskData']
for n,rec in zip(mods,t['direct_imports']):
 assert n==rec['module'];candidates=[Path(p)/(n+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(n+'.olean'))];first=candidates[0];assert first.is_file() and str(first.resolve())==rec['path'] and sha(first)==rec['sha256'];print(n,'first',first)
assert len(t['stage_receipts'])==59
for e in t['stage_receipts']:assert sha(e['path'])==e['sha256']
fresh=t['pins']['fresh_roots'];assert len(fresh)==21
for directory,files in fresh.items():
 p=Path(directory);assert p.is_dir() and not p.is_symlink() and {x.name for x in p.iterdir()}==set(files)
 for n,d in files.items():assert (p/n).is_file() and not (p/n).is_symlink() and sha(p/n)==d
om=root/'research/trace75-unscaled-reverse-graph-prototype/observations/overlay-attempt01/result.json';assert sha(om)==t['pins']['overlay_manifest']=='60f41f892354d0fb1fab6b07e15c1881a34a1e1fc9d3e9da6f2c5079d33e6845';over=json.loads(om.read_text());old,new=over['old'],over['fresh'];assert (len(old),len(new),len(set(old)&set(new)))==(1506,998,997); assert len(over['differences'])==5
for label in ('old','fresh'):
 rec=over[label];base=Path(over[label+'_root']);assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() or p.is_symlink()}==set(rec)
 for n,x in rec.items():
  p=base/n;assert str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
base=Path(over['root'])/'DiophantineConsistency';assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() or p.is_symlink()}==set(over['selected'])==set(old)|set(new)
for n,x in over['selected'].items():
 assert x==old.get(n,new.get(n));p=base/n;assert p.is_symlink() and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
for snap in [t['preflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
print('PASS outer/child/source/object/report, four first imports, 21 fresh inventories, 59 stage receipts and old-first overlay')
