#!/usr/bin/env python3
"""Reproduce the historical inherited-object environment mismatch."""
from pathlib import Path
import hashlib,json,collections,shutil
D=Path(__file__).resolve().parent;R=D.parents[3];V=R/'Computability/DiophantineConsistency/reviews';F=V/'ipra-adaptive-native-fixed-continuation/manifest.json';G=V/'ipra-adaptive-current-after-atom-plan/manifest.json';STATE=Path('/tmp/pra14-full-transitive-2x6o__to/state.json');T=STATE.parent/'transitive-manifests';OLD=Path('/tmp/pra14-full-transitive-g3ull6n_/lib');NEW=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0/lib');SNAP=V/'ipra-adaptive-fixed-snapshot-prefix/sources';h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();f=json.loads(F.read_text());g=json.loads(G.read_text());full=json.loads(STATE.read_text());anc={r['module']:r for r in full['records']};fh=h(F);gh=h(G);sth=h(STATE);ah=h(__file__)
safe=set(g['source_files'])-set(g['changed_reverse_cone'])-set(f['affected']);selected={rel.removesuffix('.olean').replace('/','.'):sha for rel,sha in f['parent_objects'].items()};selected.update({n:r['object_sha256'] for k in ['prefix_records','second_prefix_records','third_prefix_records','fourth_prefix_records'] for n,r in f[k].items()});same=[];different=[];missing=[];manifests={};mismatches={};future=set()
for n in sorted(safe):
 rec=anc.get(n)
 if not rec or not rec.get('transitive_manifest'):missing.append(n);continue
 if selected.get(n)!=rec['object_sha256']:different.append(n);continue
 same.append(n);p=T/rec['transitive_manifest'];assert h(p)==rec['transitive_manifest_sha256'];manifests[str(p)]=h(p)
 for dep,item in json.loads(p.read_text()).items():
  if item['kind']!='project':continue
  if dep in f['order']:future.add(dep)
  assert dep in selected,(n,dep)
  if selected[dep]!=item['sha256']:mismatches.setdefault(n,[]).append({'dependency':dep,'recorded':item['sha256'],'selected':selected[dep]})
assert len(same)==644 and len(different)==2 and len(missing)==34 and not future
names=['DiophantineConsistency.PRAPositiveCode','DiophantineConsistency.PRAPositivePackedNormal'];assert sorted(mismatches)==sorted(names);dep='DiophantineConsistency.PRAPositiveMapPack';assert all(len(mismatches[n])==1 and mismatches[n][0]['dependency']==dep for n in names)
rel=lambda n:Path(n.replace('.','/')+'.olean');old_obj=OLD/rel(dep);new_obj=NEW/rel(dep);old_src=STATE.parent/'source-snapshots/DiophantineConsistency_PRAPositiveMapPack.lean';new_src=SNAP/(dep.replace('.','/')+'.lean');assert h(old_obj)==anc[dep]['object_sha256'] and h(new_obj)==selected[dep] and h(old_src)==anc[dep]['source_sha256'] and h(new_src)==f['source_sha256'][dep] and h(old_obj)!=h(new_obj) and h(old_src)!=h(new_src)
for n in names:assert h(NEW/rel(n))==h(OLD/rel(n))==anc[n]['object_sha256'] and mismatches[n][0]['recorded']==h(old_obj) and mismatches[n][0]['selected']==h(new_obj)
rev=collections.defaultdict(set)
for n,ds in g['direct_project_imports'].items():
 for d in ds:rev[d].add(n)
cone=set(g['changed_vs_fixed'])|set(names);todo=list(cone)
while todo:
 for n in rev[todo.pop()]-cone:cone.add(n);todo.append(n)
assert len(cone)==247
for label,src in [('old-PRAPositiveMapPack.lean',old_src),('selected-PRAPositiveMapPack.lean',new_src),('old-PRAPositiveMapPack.olean',old_obj),('selected-PRAPositiveMapPack.olean',new_obj),('selected-PRAPositiveCode.olean',NEW/rel(names[0])),('selected-PRAPositivePackedNormal.olean',NEW/rel(names[1]))]:shutil.copyfile(src,D/label)
for n in names:shutil.copyfile(T/anc[n]['transitive_manifest'],D/anc[n]['transitive_manifest'])
assert h(F)==fh and h(G)==gh and h(STATE)==sth and h(__file__)==ah and all(h(p)==v for p,v in manifests.items()) and h(old_obj)==anc[dep]['object_sha256'] and h(new_obj)==selected[dep] and h(old_src)==anc[dep]['source_sha256'] and h(new_src)==f['source_sha256'][dep]
receipt={'status':'MISMATCH_CONFIRMED','audit_sha256':ah,'fixed_manifest_sha256':fh,'historical_graph_sha256':gh,'ancestor_state_sha256':sth,'old_source':{'path':str(old_src),'sha256':h(old_src)},'selected_source':{'path':str(new_src),'sha256':h(new_src)},'old_dependency_object':{'path':str(old_obj),'sha256':h(old_obj)},'selected_dependency_object':{'path':str(new_obj),'sha256':h(new_obj)},'mismatches':mismatches,'mismatching_ancestor_manifests':{str(T/anc[n]['transitive_manifest']):manifests[str(T/anc[n]['transitive_manifest'])] for n in names},'all_644_manifest_hashes':manifests,'ancestor_identical_checked_count':len(same),'different_from_ancestor':different,'without_ancestor_manifest':missing,'source_only_189_seeds':g['changed_vs_fixed'],'expanded_247_lower_bound':sorted(cone),'boundary':'Historical source graph only, no source-current or endpoint proof; 36 other provider origins and package-transitive/dynamic ancestry need authentication.'};(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('MISMATCH_CONFIRMED',len(same),'manifests; expanded lower bound',len(cone),'other origins',len(different)+len(missing))
