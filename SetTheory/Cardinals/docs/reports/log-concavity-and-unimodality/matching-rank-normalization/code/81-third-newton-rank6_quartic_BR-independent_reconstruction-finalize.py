"""Verify complete independent coverage and unchanged frozen inputs."""
from pathlib import Path
import json,hashlib
from collections import Counter
import reconstruct as r
OUT=Path(__file__).resolve().parent;ROOT=OUT.parent

def need(b,msg):
 if not b:raise ArithmeticError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
snapshot=json.loads((OUT/'input_snapshot.json').read_text())
for p,h in snapshot.items():need(sha(ROOT/p)==h,('input changed',p))
manifest=json.loads((ROOT/'br_manifest.json').read_text());cores=r.profiles()
need([list(v) for v in cores]==[v['core'] for v in manifest['records']],'manifest core coverage')
rows=[];counts=Counter();entries=Counter();cones=0
for core in cores:
 p=OUT/('replay_%s_%s_%s_%s.json'%core);v=json.loads(p.read_text())
 need(v['core']==list(core) and v['all_pass'] and v['basis_instances']==51,'independent profile coverage')
 pp=ROOT/('br_%s_%s_%s_%s.json'%core);prod=json.loads(pp.read_text())
 need(sha(pp)==v['producer_record_sha256'],'producer linkage')
 need(prod==next(z for z in manifest['records'] if z['core']==list(core)),'manifest and record differ')
 by={tuple(z['basis']):z for z in prod['records']}
 need([tuple(z['basis']) for z in v['records']]==list(r.BASES),'independent basis order')
 for z in v['records']:
  x=by[tuple(z['basis'])];need(z['terms']==x['terms'] and z['sha256']==x['sha256'],'full hash replay')
 counts[core[0]]+=1;entries[core[0]]+=v['coefficient_entries'];cones+=51
 rows.append({'core':list(core),'independent_file':p.name,'independent_sha256':sha(p),'producer_record_sha256':sha(pp),'coefficient_entries':v['coefficient_entries'],'seconds':v['seconds']})
e=json.loads((OUT/'endpoint_checks.json').read_text());need(e['all_pass'] and e['q_BR_pair_profile_checks']==89,'endpoint audit')
categories=json.loads((OUT/'category_checks.json').read_text());need(categories['all_pass'] and categories['generic_columns_remain_distinct'],'category audit')
need(sum(entries.values())==43344919==manifest['coefficient_entries'],'total entries')
need(cones==4539==manifest['basis_instances'],'total cones')
need(dict(counts)=={1:24,3:40,7:25},'profiles')
need(dict(entries)=={1:11820833,3:19282707,7:12241379},'per-root totals')
result={'all_pass':True,'profiles':89,'basis_instances':cones,'coefficient_entries':sum(entries.values()),'profiles_by_U':dict(counts),'entries_by_U':dict(entries),'endpoint_polynomial_checks':e['endpoint_polynomial_checks'],'q_BR_pair_profile_checks':89,'category_and_union_equalities':categories['category_and_union_equalities'],'independent_R_blocks':len({(c[0],c[1]) for c in cores}),'immutable_input_files_checked':len(snapshot),'input_manifest_sha256':sha(ROOT/'br_manifest.json'),'independent_source_sha256':sha(OUT/'reconstruct.py'),'all_ordered_coefficient_hashes_match':True,'all_reconstructed_coefficients_nonnegative':True,'seconds_sum':sum(z['seconds'] for z in rows),'records':rows}
(OUT/'independent_manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
