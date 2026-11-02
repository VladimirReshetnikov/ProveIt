#!/usr/bin/env python3
"""Independent source-closure survey only: no Lean build is performed."""
import hashlib,json,re,subprocess,shutil
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';PLAN=BASE/'research/ordinary12-ipra-bridge/difference-ring-build-plan';SNAP=Path('/tmp/ipra-aq29-fresh-source-closure-v2');PARENT=Path('/tmp/ipra-aq29-fresh-project-pair/author/state.json');RANK=BASE/'research/ordinary12-ipra-bridge/rank-adapter-prototype/replay-receipt.json'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def J(p):return json.loads(Path(p).read_text())
def git(p):return subprocess.check_output(['git','show',f'{head}:{p}'],cwd=ROOT)
def imports(raw):return [m.group(1).decode() for m in re.finditer(rb'^import[ \t]+([^ \t\r\n]+)',raw,re.M)]
a=J(PLAN/'model-closure-manifest.json');old=J(SNAP/'manifest.json')['sources'];rank=J(RANK);parent=J(PARENT);obs=J(PLAN/'observation.json');head=a['head']
assert head=='09bdb5b03a3f39c8795b8292e6f0a87296373efd' and H(PLAN/'model-closure-manifest.json')=='859169fa08540764d0b02864fdeb7906301afcf4e1fea1e4b0e689c90df491b4' and H(SNAP/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48' and H(RANK)=='955f79233a43e2500aa2f477a51bc097ad419604b2306e908ff9fd54236d2a06' and H(PARENT)=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
for path,key in [('lakefile.toml','lakefile_sha256'),('lean-toolchain','lean_toolchain_sha256')]:
 raw=git(path);assert hashlib.sha256(raw).hexdigest()==a[key] and (ROOT/path).read_bytes()==raw
for name in ('README.md','audit_plan.py','model-closure-manifest.json','observation.json'):
 p=PLAN/name;assert subprocess.check_output(['git','show','bf1590bbbc:'+str(p.relative_to(ROOT))],cwd=ROOT)==p.read_bytes()
model=a['sources'];rankset=set(rank['source_closure']);union=set(model)|rankset;assert (len(model),len(rankset),len(union))==(19,62,64)
changed=[];new=[];raws={};model_edges={};historic_edges={}
for n in sorted(union):
 row=model.get(n) or old[n];raw=git(row['workspace_path']);raws[n]=raw;assert (ROOT/row['workspace_path']).read_bytes()==raw
 if n in model:assert H(SNAP/'manifest.json') and hashlib.sha256(raw).hexdigest()==model[n]['sha256'] and imports(raw)==model[n]['imports'];model_edges[n]=imports(raw)
 if n not in old:new.append(n)
 else:
  oldraw=(SNAP/old[n]['snapshot_path']).read_bytes();assert hashlib.sha256(oldraw).hexdigest()==old[n]['sha256'] and imports(oldraw)==old[n]['imports'];historic_edges[n]=imports(oldraw)
  if raw!=oldraw:changed.append(n)
assert new==['DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.WeightedExpressionDegree'] and changed==['DiophantineConsistency.NaturalExpression']
# Reconstruct the source-only target closure independently from parsed pinned blobs.
seen=set();external=set();todo=['DiophantineConsistency.ModelDifferenceRing']
while todo:
 n=todo.pop()
 if n in seen:continue
 if n not in model:external.add(n);continue
 seen.add(n);todo.extend(model_edges[n])
assert seen==set(model) and external==set(a['external_modules']) and len(external)==17
assert set(a['order'])==seen and len(a['order'])==len(seen)
positions={n:i for i,n in enumerate(a['order'])}
assert all(positions[dep]<positions[n] for n in seen for dep in model_edges[n] if dep in seen)
reverse=set(changed)
while True:
 nextset=reverse|{n for n in rankset if any(dep in reverse for dep in historic_edges[n])}
 if nextset==reverse:break
 reverse=nextset
assert len(reverse)==27
records={r['module']:r for r in parent['records']}
for n in rankset:assert records[n]['source_sha256']==old[n]['sha256']
seenrank=set();todo=['DiophantineConsistency.ArithmeticAdaptiveFactorThree2011','DiophantineConsistency.ArithmeticAdaptiveMersenne2011']
while todo:
 n=todo.pop()
 if n in seenrank or n not in old:continue
 seenrank.add(n);todo.extend(historic_edges[n])
assert seenrank==rankset
def project_bytes(ns):
 total=0
 for n in ns:
  assert records[n]['exit']==0 and H(records[n]['log'])==records[n]['log_sha256']
  outputs=parent['outputs'][n];present=[(p,m) for p,m in outputs.items() if m is not None];assert len(present)==1
  for p,m in present:
   path=Path(p);assert path.is_file() and not path.is_symlink() and H(path)==m['sha256']==records[n]['object_sha256'];total+=path.stat().st_size
 return total
allbytes=project_bytes(rankset);affectedbytes=project_bytes(reverse)
assert allbytes==obs['historical_62_output_bytes']==42965976 and affectedbytes==obs['historical_27_affected_output_bytes']==19274200
assert obs['status']=='SOURCE_ONLY_NOT_COMPILED' and obs['freeze_exit_code']==obs['audit_exit_code']==0
modeltext=raws['DiophantineConsistency.ModelDifferenceRing'].decode()
for x in ['def DiffRing : Type _ := Quotient (setoid V)','instance : CommRing (DiffRing V)','theorem split_evalRing','theorem internalZero_iff']:assert x in modeltext
# Controls on independently reconstructed reverse closure and source pins.
assert len(reverse-{next(iter(reverse))})==26
bad=bytearray(raws['DiophantineConsistency.NaturalExpression']);bad.append(32);assert hashlib.sha256(bad).hexdigest()!=model['DiophantineConsistency.NaturalExpression']['sha256']
text=(PLAN/'README.md').read_text();assert 'planning budget, not a cap' in text and 'sampling cannot guarantee' in text and 'not an aggregate project-tree quota' in text and 'does not by itself guarantee 4 GiB of host free space' in text
report={'status':'PASS_INDEPENDENT_DIFFERENCE_RING_SOURCE_PLAN_AUDIT','frozen_git_head':head,'model_manifest_sha256':H(PLAN/'model-closure-manifest.json'),'historical_manifest_sha256':H(SNAP/'manifest.json'),'model_source_modules':len(model),'historical_rank_modules':len(rankset),'union_modules':len(union),'model_external_modules':len(external),'new_modules':new,'changed_modules':changed,'historic_reverse_dependents':sorted(reverse),'historic_outputs_bytes':allbytes,'historic_reverse_outputs_bytes':affectedbytes,'current_tmp_free_bytes':shutil.disk_usage('/tmp').free,'historical_free_bytes_recorded':obs['disk_available_bytes'],'seven_generated_objects_bytes_recorded':obs['seven_generated_objects_bytes'],'scope':'Static source/header survey only; no compiler-authoritative import graph, new bridge, build, runtime resource reservation, package-transitive ancestry or iPRA proof.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing overwrite')
out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');print(report['status'],H(out))
