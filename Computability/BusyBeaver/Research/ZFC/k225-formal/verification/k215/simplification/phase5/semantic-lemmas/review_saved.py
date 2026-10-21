"""Read saved isolated source/log evidence; never run Lean or archived programs."""
from pathlib import Path,PurePosixPath
import argparse,difflib,hashlib,json,re,tarfile
BAD={'.olean','.ilean','.o','.so','.a','.vo','.vos','.vok','.glob','.pyc','.pyo'}
AXIOMS={'propext','Classical.choice','Quot.sound'}
def digest(b):return hashlib.sha256(b).hexdigest()
def validate(members,summary):
 read=lambda n:json.loads(members[n])
 paths=read('paths.json')
 for entry in paths.values():
  b=members[entry['member']];assert len(b)==entry['bytes'] and digest(b)==entry['sha256']
 def original(path):return members[paths[path]['member']]
 def diff(before,after,path):
  d=members[path].decode();head=d.splitlines()
  assert head[0].startswith('--- ') and head[1].startswith('+++ ')
  expected=''.join(difflib.unified_diff(members[before].decode().splitlines(True),members[after].decode().splitlines(True),fromfile=head[0][4:],tofile=head[1][4:]))
  assert d==expected,path
 diff('constructible/ConstructibleAbs.before.lean','constructible/ConstructibleAbs.lean','constructible/source.diff')
 diff('internal-sat/baseline/InternalSat.lean','internal-sat/InternalSat.lean','internal-sat/source-final.diff')
 records={};sources=[]
 selected={
 'constructible':{'run1':'FAIL','run2':'PASS','run3':'FAIL','run4':'FAIL','run5':'PASS','audit-baseline':'PASS','audit-candidate':'PASS'},
 'internal-sat':{'run1':'FAIL','run2':'PASS','run3':'PASS','baseline-run1':'PASS'}}
 for family,runs in selected.items():
  for run,status in runs.items():
   folder=family+'/'+run;r=read(folder+'/result.json');records[folder]=r
   srcpath=r.get('source_snapshot',r.get('source',r['command'][-1]));src=original(srcpath)
   log=members[folder+'/compiler.log'].decode()
   assert digest(src)==r['source_sha256'] and digest(log.encode())==r['log_sha256']
   assert r['command'][-1]==srcpath and r['command'][1:3]==['-j1','-M12288']
   assert r['command'][3].startswith('--root=') and r['command'][4]=='-o'
   assert len(r['command'])==7 and r['command'][5].endswith('.olean')
   assert r['timeout_seconds']==120 and r['memory_mebibytes']==12288
   assert r['status']==status and r['timed_out'] is False and r['seconds']>=0 and r['lock_wait_seconds']>=0
   assert r['warnings']==log.count('warning:')
   if status=='PASS':
    assert r['exit_code']==0 and r['warnings']==0 and 'error:' not in log and 'sorryAx' not in log and "declaration uses 'sorry'" not in log
    assert re.fullmatch('[0-9a-f]{64}',r['object_sha256'])
   else:assert r['exit_code']!=0 and 'error:' in log
   if family=='constructible' and run.startswith('run'):
    assert r['basis_unchanged'] and r['source_unchanged'] and len(r['basis_objects'])==185
    assert r['runner_sha256']==digest(members['constructible/run.py'])
   if family=='internal-sat':
    assert r['canonical_unchanged'] and r['inputs_unchanged'] and r['providers_unchanged'] and r['basis_unchanged']
    assert r['supervisor_sha256']==digest(members['internal-sat/check.py'])
    reports=re.findall(r'depends on axioms: \[([^]]*)\]',log)
    assert reports==r['axiom_reports']
    if status=='PASS':assert len(reports)==3 and all({a.strip() for a in x.split(',')}<=AXIOMS for x in reports)
   sources.append(digest(src))
 compiler={r['compiler_sha256'] for r in records.values()};basis={r['basis_completed_sha256'] for r in records.values()}
 assert len(compiler)==len(basis)==1
 c=read('constructible/comparison.json');i=read('internal-sat/comparison-final.json')
 cf=summary['features']['ConstructibleAbs'];inf=summary['features']['InternalSat']
 for feature,before,after in [(cf,'constructible/ConstructibleAbs.before.lean','constructible/ConstructibleAbs.lean'),(inf,'internal-sat/baseline/InternalSat.lean','internal-sat/InternalSat.lean')]:
  assert digest(members[before])==feature['baseline_sha256'] and digest(members[after])==feature['source_sha256']
  for prefix,path in [('before',before),('after',after)]:
   assert len(members[path])==feature[prefix+'_bytes'] and len(members[path].splitlines())==feature[prefix+'_lines']
  r=read(feature['final_run']);assert feature['seconds']==r['seconds'] and feature['warnings']==r['warnings']==0
 assert c['candidate_sha256']==cf['source_sha256'] and c['public_declarations_preserved']==73 and c['executable_definitions_unchanged']==7
 assert i['candidate_sha256']==inf['source_sha256'] and i['unchanged_original_headers']==79 and i['unchanged_definitions_and_structures']==30
 assert digest(members['constructible/run5/result.json'])==c['kernel_run_sha256']
 assert digest(members['internal-sat/run3/result.json'])==i['candidate_result_sha256']
 assert members['constructible/ConstructibleAbs.lean']==original(records['constructible/run5']['source'])
 assert members['internal-sat/InternalSat.lean']+members['internal-sat/Audit.lean.inc']==original(records['internal-sat/run3']['source_snapshot'])
 cb,cc=(records['constructible/'+n] for n in ['audit-baseline','audit-candidate'])
 assert cb['source_sha256']==cc['source_sha256']==digest(members['constructible/Audit.lean'])
 assert cb['reports']==cc['reports']==read('constructible/api-comparison.json')['reports'] and len(cc['reports'])==5
 for run in ['audit-baseline','audit-candidate']:
  log=members['constructible/'+run+'/compiler.log'].decode()
  reported=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
  assert [list(x) for x in reported]==records['constructible/'+run]['reports']
  assert all({a.strip() for a in x[1].split(',')}<=AXIOMS for x in reported)
 assert cc['module_object_sha256']==records['constructible/run5']['object_sha256']
 assert records['internal-sat/baseline-run1']['axiom_reports']==records['internal-sat/run3']['axiom_reports']
 cp=read('peer/constructible/review.json');ip=read('peer/internal-sat/final-review.json')
 assert cp['files']['ConstructibleAbs.lean']==cf['source_sha256'] and ip['source_sha256']==inf['source_sha256']
 assert ip['prior_peer_sha256']==digest(members['peer/internal-sat/review.json'])
 assert ip['new_actual_sha256']==digest(members['internal-sat/run3/result.json'])
 return {'isolated_attempts':11,'preserved_failures':4,'module_passes':4,'api_only_passes':3,
         'constructible_axiom_reports_per_api_run':5,'internal_sat_axiom_reports_per_passed_run':3,
         'exact_final_source_and_diff_bindings':True,'saved_compiler_sha256':next(iter(compiler)),
         'saved_basis_completed_sha256':next(iter(basis))}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert not a.output.exists();p=a.packet;summary=json.loads((p/'result.json').read_text());index=json.loads((p/'index.json').read_text())
 assert summary['status']=='PRESERVED_ISOLATED_KERNEL_AND_API_EVIDENCE'
 archive=p/'evidence.tar.gz';assert digest(archive.read_bytes())==summary['archive_sha256']
 members={}
 with tarfile.open(archive,'r:gz') as stream:
  for entry in stream:
   path=PurePosixPath(entry.name)
   assert entry.isfile() and not path.is_absolute() and '..' not in path.parts and not(set(path.suffixes)&BAD) and entry.name not in members
   data=stream.extractfile(entry).read();assert index[entry.name]=={'sha256':digest(data),'bytes':len(data)};members[entry.name]=data
 assert set(members)==set(index) and len(members)==summary['archive_members'] and summary['compiled_objects_in_archive'] is False
 assert members['publication/review_saved.py']==(p/'review_saved.py').read_bytes()
 for n in ['constructible/source.diff','constructible/comparison.json','constructible/api-comparison.json',
           'internal-sat/source-final.diff','internal-sat/comparison-final.json','peer/constructible/review.json',
           'peer/internal-sat/review.json','peer/internal-sat/final-review.json']:
  assert (p/n).read_bytes()==members[n]
 checked=validate(members,summary)
 result={'status':'PASS_SAVED_FEATURE_EVIDENCE_REVIEW',**checked,'archive_members':len(members),'archive_sha256':digest(archive.read_bytes()),
         'reviewer_sha256':digest(Path(__file__).read_bytes()),'scope':'Archive integrity and exact retained source/diff/record/log/API/peer bindings. No compiler, archived-code execution, full closure audit or live-provider check.'}
 with a.output.open('x') as out:json.dump(result,out,indent=2);out.write('\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
