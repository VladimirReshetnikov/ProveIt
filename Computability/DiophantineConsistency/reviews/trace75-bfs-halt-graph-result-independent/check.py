from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2]; h=root/'research/trace75-bfs-halt-graph-prototype'; a=h/'observations/directbfshalt80-attempt03'; o=h/'observations/outer-attempt03'; t=json.loads((a/'terminal.json').read_text()); out=json.loads((o/'result.json').read_text()); obj=Path(t['output_root'])/'Trace75BFSHaltGraph.olean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'terminal.json')=='2e046b096e061fc4754f2865ace97ad8d1d7a8ddea203243e891d840443f59c1'
assert sha(o/'result.json')=='719738b12906e3105d3d3df0dfb6ad2757396a9387278ef3c7ebb11e548b3f1f'
assert t['exit']==0 and t['reason'] is None and t['pins']==t['after'] and t['direct_imports']==t['direct_imports_after']
assert out['child_exit']==0 and out['terminal_sha256']==sha(a/'terminal.json') and out['inputs_before']==out['inputs_after'] and out['wrapper_before']==out['wrapper_after']==sha(h/'run-outer.py')=='b2b411ef12b83235c69f212a6876ccce1eb7466ce15f9923b1dbcbb7ca2a28ee'
for p,d in out['inputs_before'].items():assert sha(p)==d
for n in ('stdout','stderr'): assert sha(o/n)==out[n+'_sha256'] and sha(a/n)==t[n+'_sha256']
src=h/'Trace75BFSHaltGraph.lean'; assert sha(src)==sha(a/'source.txt')==sha(obj.with_suffix('.lean'))==t['pins']['source']=='9ad0f1b7a90c8305d95978024881382a6b88e9c3794cdc7c1447c4220a29957d'
assert sha(h/'run-v3.py')==t['pins']['runner']=='5d32b766ba402d9ed2c926fda5ec7f0e78a93bfea8854b90b517a63532222909'
assert obj.is_file() and not obj.is_symlink() and sha(obj)==t['object_sha256']=='93e589ad5e0151f262966bbee34c7a27b35b1e192c4a4de1679fcc8a0716014d'
assert (a/'stdout').read_text()=="'Trace75BFSHaltGraph.halt_zero_of_model_ports' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (a/'stderr').read_bytes()
mods=re.findall(r'^import\s+([^\s]+)',src.read_text(),re.M); assert mods==['DirectBFSHaltPellSeed','Trace75PackingReverseGraph','CompactRankResidueJoin','Direct80RankLower']
for n,rec in zip(mods,t['direct_imports']):
 assert n==rec['module']; candidates=[Path(p)/(n+'.olean') for p in t['lean_path'].split(':') if os.path.lexists(Path(p)/(n+'.olean'))]; first=candidates[0]; assert first.is_file() and str(first.resolve())==rec['path'] and sha(first)==rec['sha256']; print(n,'first',first)
assert len(t['stage_receipts'])==59
for e in t['stage_receipts']:assert sha(e['path'])==e['sha256']
om=root/'research/trace75-unscaled-reverse-graph-prototype/observations/overlay-attempt01/result.json'; assert sha(om)==t['pins']['overlay_manifest']=='60f41f892354d0fb1fab6b07e15c1881a34a1e1fc9d3e9da6f2c5079d33e6845'; overlay=json.loads(om.read_text())
old,fresh=overlay['old'],overlay['fresh']; assert (len(old),len(fresh),len(set(old)&set(fresh)))==(1506,998,997)
diff=sorted(n for n in set(old)&set(fresh) if old[n]['sha256']!=fresh[n]['sha256']); assert diff==overlay['differences'] and len(diff)==5
for label in ('old','fresh'):
 rec=overlay[label]; base=Path(overlay[label+'_root']); assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() or p.is_symlink()}==set(rec)
 for n,x in rec.items():
  p=base/n; assert str(p)==x['path'] and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
base=Path(overlay['root'])/'DiophantineConsistency'; assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() or p.is_symlink()}==set(overlay['selected'])==set(old)|set(fresh)
for n,x in overlay['selected'].items():
 assert x==old.get(n,fresh.get(n)); p=base/n; assert p.is_symlink() and str(p.resolve(strict=True))==x['target'] and sha(p)==x['sha256']
for snap in [t['preflight'],*t['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
print('PASS outer/child receipts, source/object/report, 4 direct imports, 59 stage receipt hashes and all overlay inventories')
