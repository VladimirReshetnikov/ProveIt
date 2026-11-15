#!/usr/bin/env python3
"""Offline verification of the frozen comparison packet (Python standard library).

Checks inventory consistency, representative matrices, exact 194-state
canonical tuples, new-table novelty, and the finite logical proof templates.
It is not a consistency proof or a proof-assistant kernel check.
"""
from pathlib import Path
import argparse,collections,csv,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
if not __debug__:raise RuntimeError('Run without Python -O')
HERE=Path(__file__).resolve().parent

def read(name):return json.loads((HERE/name).read_text())
def module(name,filename):
 spec=importlib.util.spec_from_file_location(name,HERE/filename);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);args=p.parse_args()
 manifest=read('MANIFEST.json');errors=[]
 for rec in manifest['files']:
  b=(HERE/rec['path']).read_bytes()
  if len(b)!=rec['size'] or hashlib.sha256(b).hexdigest()!=rec['sha256']:errors.append(rec['path'])
 assert not errors,('manifest mismatch',errors)
 packets=read('packet_ledger93.json');assert len(packets)==93
 occ,ids,classes=[read('current/'+n+'.json')for n in ['occurrences','identities','classes']]
 assert(len(occ),len(ids),len(classes))==(4468,879,728)
 assert sum(r['spanning']for r in classes)==721
 distribution=read('current/all_size_distribution.json')
 for rec in distribution:
  n=rec['states'];assert rec['matrix_occurrences']==sum(r['states']==n for r in occ)
  assert rec['normalized_labeled_identities']==sum(r['states']==n for r in ids)
  assert rec['spanning_graph_classes']==sum(r['states']==n and r['spanning']for r in classes)
  assert rec['nonspanning_literal_identities']==sum(r['states']==n and not r['spanning']for r in classes)
 c=module('packet_census','rebuild_current_census.py')
 represented=0
 for rec in classes:
  local=rec.get('local_representative')
  if not local:continue
  b=(HERE/'current'/local).read_bytes();d=c.ji.lib.parse_table(b)
  assert d is not None and len(d[1])==rec['states']
  assert hashlib.sha256(c.normalized_text(d).encode()).hexdigest()==rec['normalized_sha256']
  represented+=1
 refs={key:tuple(tuple(r)for r in value)for key,value in read('current/canonical_tuples194.json').items()}
 frontier=[r for r in read('current/classes194.json')if r['spanning']];assert len(frontier)==len(refs)==139
 def canonical(data):
  forms=[]
  for root in data[1]:
   for mirror in (False,True):
    for complement in (False,True):
     form,n=c.full_tuple(data,root,mirror,complement,True)
     if n==len(data[1]):forms.append(form)
  assert forms,'No spanning root';return min(forms)
 for rec in frontier:
  d=c.ji.lib.parse_table((HERE/'current'/rec['local_representative']).read_bytes())
  assert canonical(d)==refs[rec['table_class']],rec['table_class']
 assert len(set(refs.values()))==139
 novelty=[];new=[]
 for path in sorted((HERE/'candidates').glob('*/machine.tm')):
  b=path.read_bytes();d=c.ji.lib.parse_table(b);form=canonical(d)
  assert len(d[1])==194 and len(d[0])==388
  assert form not in refs.values() and form not in new,path
  new.append(form);novelty.append({'machine':path.parent.name,'sha256':hashlib.sha256(b).hexdigest(),'states':len(d[1]),'novel_against139_and_earlier_candidates':True,'enlarged_symmetry_sha256':hashlib.sha256(json.dumps(form,separators=(',',':')).encode()).hexdigest()})
 j=module('verify_j','verify_j.py');ja=module('verify_ja','verify_ja.py')
 logical=[j.check(HERE/'j_certificates'/name)for name in ['h1_to_J.json','J_to_h1.json']]
 logical += [ja.check(HERE/'ja_certificates'/name)for name in ['old_to_JA.json','JA_to_h1.json']]
 base=module('verify_logic','verify_logic.py')
 logical += [base.check(path)for path in sorted((HERE/'logical_certificates').glob('*.json'))if path.name!='generation.json']
 audit=read('current/full_source_blob_verification.json');assert audit['status']=='PASS' and audit['files_checked']==27459 and not audit['errors']
 b=read('current/control_bisimulation.json');assert b['tables']==139 and b['all_singleton']
 result={'status':'PASS','source_pin':manifest['source_pin'],'manifest_files_checked':len(manifest['files']),'deliveries':len(packets),'recognized_matrix_occurrences':len(occ),'normalized_labeled_identities':len(ids),'spanning_graph_classes':721,'nonspanning_literal_identities':7,'included_representative_tables':represented,'recomputed194_enlarged_canonical_tuples':139,'new_table_novelty':novelty,'logical_certificates':logical,'scope':'Finite structural and syntactic checks. No new end-to-end Lean theorem; historical calibrations are attributed written inputs.'}
 text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 print(text)
if __name__=='__main__':main()
