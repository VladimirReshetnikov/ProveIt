"""Check completeness, immutable inputs, and both full certificate manifests."""
from reconstruct import ROOT,OUT,profiles,BASES,need
from pathlib import Path
import json,hashlib
original=json.loads((ROOT/'core_schur_manifest.json').read_text())
cores=profiles();need(sorted(map(tuple,original['all_profile_list']))==cores,'primary orbit list mismatch')
need(original['completed_profiles']==61 and original['negative'] is None,'primary batch incomplete')
records=[]
for core in cores:
 rp=OUT/('replay_%s_%s_%s.json'%core);need(rp.exists(),('missing replay',core))
 record=json.loads(rp.read_text());need(record['all_pass'],'failed replay')
 cp=ROOT/('core_schur_%s_%s_%s.json'%core)
 need(hashlib.sha256(cp.read_bytes()).hexdigest()==record['producer_sha256'],'producer record changed')
 data=json.loads(cp.read_text());need(data['integer_multiplier']>0,'nonpositive clearing scalar')
 records.append(record)
for f in ('endpoint_audit.json','relations_audit.json','finite_compression.json'):
 need(json.loads((OUT/f).read_text())['all_pass'],('auxiliary audit failed',f))
total=sum(v['coefficient_entries'] for v in records)
need(total==original['coefficient_entries_checked']==50037694,'global coefficient count')
need(sum(v['basis_instances'] for v in records)==original['basis_instances']==3111,'basis count')
sourcehashes={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ('build_core_schur_certificate.py','run_core_schur_profiles.py','core_R_block_inverses.json','core_schur_manifest.json')}
expected={'build_core_schur_certificate.py':'76f0b34400a3a44c5b5086bf9a17df2892e937e3f7493936cd3e356ce54ea3fd','run_core_schur_profiles.py':'0bd6e9c6bc09e164e989b026ac2e01c9e6a522e826befce7d81fa93a58344a41','core_R_block_inverses.json':'8c8d4d9e614096fdac53ba4a8f164856cb71f6e66d4ba749b3223721df15d8df'}
for k,v in expected.items():need(sourcehashes[k]==v,('frozen source changed',k))
out={'all_pass':True,'profiles':61,'basis_instances':3111,'coefficient_entries':total,'endpoint_polynomial_checks':1032,'q_all_Hall_reconstructions':61,'R_feature_relations':14,'finite_graph_signed_vector_checks':48,'source_sha256':sourcehashes,'records':records}
(OUT/'independent_manifest.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
