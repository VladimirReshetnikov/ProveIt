#!/usr/bin/env python3
"""Independent structural/hash check only. Does not invoke Lean or Lake."""
from pathlib import Path
import hashlib,json,difflib
OUT=Path(__file__).resolve().parent
FIX=OUT/'fixtures'
manifest=json.loads((FIX/'source_manifest.json').read_text())
if manifest['commit'] != 'e1c8914bc7064d9a8e7c06171a18069a949badd0':
 raise RuntimeError('Wrong source manifest pin')
entries={v['path']:v for v in manifest['sources']}
cases=[
 ('IterationSize.lean',FIX/'IterationSize.candidate.lean',['iterate_depth']),
 ('SidonPositions.lean',FIX/'SidonPositions.candidate.lean',['weight_injective','pairWeight_injective']),
 ('WangTiles942PhysicalOrder.lean',FIX/'WangTiles942PhysicalOrder.candidate.lean',['strictMono_fin_eq_self']),
 ('CurrentPowerCoordinates2011.lean',FIX/'CurrentPowerCoordinates2011.candidate.lean',['generator_cast_auxiliary','generator_cast_C0'])]
info=[]
for name,candidate,targets in cases:
 rel='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name
 a=(FIX/name.replace('.lean','.source.lean')).read_bytes();b=candidate.read_bytes();meta=entries[rel]
 sha=hashlib.sha256(a).hexdigest();blob=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()
 changed=[{'kind':tag,'source_start':i+1,'source_end':j,'candidate_start':k+1,'candidate_end':l,'removed':a.decode().splitlines()[i:j],'added':b.decode().splitlines()[k:l]} for tag,i,j,k,l in difflib.SequenceMatcher(a=a.decode().splitlines(),b=b.decode().splitlines()).get_opcodes() if tag!='equal']
 statements=[]
 for target in targets:
  sa=a.decode().split('theorem '+target,1)[1].split(':=',1)[0]
  sb=b.decode().split('theorem '+target,1)[1].split(':=',1)[0]
  statements.append({'theorem':target,'statement_identical':sa==sb})
 row={'file':rel,'candidate_path':str(candidate.relative_to(OUT)),'source_manifest_sha256_matches':sha==meta['sha256'],'source_git_blob_matches':blob==meta['sha'],'source_sha256':sha,'candidate_sha256':hashlib.sha256(b).hexdigest(),'source_lines':len(a.splitlines()),'candidate_lines':len(b.splitlines()),'source_delta_lines':len(a.splitlines())-len(b.splitlines()),'statements':statements,'changed_regions':changed,'validation':'source inspection only; no Lean invocation'}
 if not (row['source_manifest_sha256_matches'] and row['source_git_blob_matches'] and all(x['statement_identical'] for x in statements)):
  raise RuntimeError(f'Source identity or theorem statement mismatch: {name}')
 row['novelty_status'] = 'EXCLUDED_EXACT_DUPLICATE_CLOSING_ZH' if name == 'WangTiles942PhysicalOrder.lean' else 'RETAINED_AFTER_CLOSING_SCREEN'
 row['eligible_new_lines_saved'] = 0 if name == 'WangTiles942PhysicalOrder.lean' else row['source_delta_lines']
 info.append(row)
mathlib=[]
for binding,path in [('FinBasic_binding.json','FinBasic.lean'),('EquivDefs_binding.json','Logic_Equiv_Defs.lean')]:
 meta=json.loads((FIX/binding).read_text()); data=(FIX/path).read_bytes()
 gotsha=hashlib.sha256(data).hexdigest();gotblob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 record={'path':meta['path'],'sha256_matches':gotsha==meta['sha256'],'git_blob_matches':gotblob==meta['sha'],'pinned_revision_matches':meta['commit']=='81a5d257c8e410db227a6665ed08f64fea08e997'}
 if not all(record[k] for k in ['sha256_matches','git_blob_matches','pinned_revision_matches']):
  raise RuntimeError(f'Mathlib evidence binding mismatch: {path}')
 mathlib.append(record)
result={'pin':manifest['commit'],'files':info,'mathlib_binding_checks':mathlib,'total_reviewed_source_delta':sum(x['source_delta_lines'] for x in info),'eligible_new_lines_saved':sum(x['eligible_new_lines_saved'] for x in info),'accounting_note':'Sidon raw-source168→164; assumed prior161→new157. Prior7 not reclaimed.','proof_status':'UNCOMPILED'}
(OUT/'structural_check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'files':len(info),'statements':sum(len(x['statements']) for x in info),'reviewed_source_delta':result['total_reviewed_source_delta'],'eligible_new_lines_saved':result['eligible_new_lines_saved'],'mathlib_bindings_verified':len(mathlib),'proof_status':'UNCOMPILED'},indent=2))
