#!/usr/bin/env python3
"""Build a signed thirteen-integer trace/F16 sibling from pinned inert DAGs."""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'candidates/integer13-quadratic-trace'
PREFIX=ROOT/'candidates/constructive-integer14-quadratic-shared'
NORM=ROOT/'candidates/constructive-integer14-shared'
TRACE=ROOT/'candidates/interpolation-shared-norms'
PINS={
 'prefix':'307015e68eb300713d06076b0c3c78f1017fe74dbe79f6b89385292637d1ec41',
 'norm':'0e9f89dfdcc8a27feed8a278d46b04b10c88d24cec76a190444eb9b7e2b0fa7b',
 'trace':'08736b9eba62494821c7b4b46b58eca6936025adf51efb33382fd54e9c822190',
}
OPS={'add','sub','mul'}

def need(ok,message):
 if not ok:raise ValueError(message)

def digest(raw):return sha256(raw).hexdigest()
def encoded(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()

def build():
 prefix_raw=(PREFIX/'equation.json').read_bytes()
 norm_raw=(NORM/'equation.json').read_bytes()
 trace_raw=(TRACE/'integer13_trace_degree1072.json').read_bytes()
 for name,raw in [('prefix',prefix_raw),('norm',norm_raw),('trace',trace_raw)]:
  need(digest(raw)==PINS[name],'entire frozen '+name+' DAG')
 parent=json.loads(prefix_raw);n=parent['nodes'];nm=parent['named_registers']
 need(n[95]==['mul',92,94]and n[94]==['mul',5,5]and
      n[105]==['sub',103,104]and n[104]==['mul',13,13]and
      n[13]==['variable','p1'],'exact two guard rewrites')
 nodes=[];mapping={};records=[]
 removed={13,94,104,111}
 aliases={95:92,105:103}
 for i,row in enumerate(n[:125]):
  if i in removed:
   records.append(dict(parent=i,status='deleted',old_row=row));continue
  if i in aliases:
   mapping[i]=mapping[aliases[i]]
   records.append(dict(parent=i,status='alias',child=mapping[i],source_parent=aliases[i],old_row=row));continue
  newrow=([row[0],mapping[row[1]],mapping[row[2]]]if row[0]in OPS else deepcopy(row))
  mapping[i]=len(nodes);nodes.append(newrow)
  records.append(dict(parent=i,status='retained',child=mapping[i]))
 E=len(nodes);nodes.append(['mul',mapping[110],mapping[114]])
 prefix_length=len(nodes)
 oldnorm=json.loads(norm_raw);old=oldnorm['nodes']
 cuts={122:mapping[121],123:mapping[122],124:mapping[123],126:E,
       127:mapping[124],68:mapping[68],28:mapping[28],60:mapping[60]}
 fmap=dict(cuts);memo={tuple(row):i for i,row in enumerate(nodes)}
 def visit(i):
  if i in fmap:return fmap[i]
  row=old[i]
  nr=[row[0],visit(row[1]),visit(row[2])]if row[0]in OPS else deepcopy(row)
  key=tuple(nr)
  if key not in memo:memo[key]=len(nodes);nodes.append(nr)
  fmap[i]=memo[key];return fmap[i]
 output=visit(oldnorm['named_registers']['N'])
 names={k:mapping[i]for k,i in nm.items()if i in mapping and k not in('guard','Gv','S','output')}
 names.update(Ag=mapping[110],raw_A=mapping[122],raw_B=mapping[123],
              scaled_Ag=E,N=output,output=output)
 counts=dict(Counter(row[0]for row in nodes if row[0]in OPS))
 need(len(nodes)==162 and counts=={'mul':81,'add':27,'sub':27},'literal135 operations')
 variables=[name for name in parent['variables']if name!='p1']
 equation=dict(schema='integer-polynomial-dag-v1',name='integer13_quadratic_trace_degree536',
  domain='unrestricted integers',variables=variables,variable_count=13,nodes=nodes,
  output=output,named_registers=names,operation_counts=counts,operations=sum(counts.values()),
  exact_degree=536,coefficient_binding='coefficients/BINDING.json',
  coefficient_binding_detail='Whole six-port mixed-parity-unrounded-1064921 tuple; MF already shifted once.',
  proof='PROOF.md',proof_status='Ordinary unbounded integer-existence equivalence with pinned trace13 kernel; no new Lean/internal-ZFC proof.',
  defining_polynomial='delta^8 F16(Z;U^2 Df,U^2 Dtau,U^2 Ag,U^2 Cy/delta)')
 files={'equation.json':encoded(equation),'source/prefix-equation.json':prefix_raw,
        'source/norm-equation.json':norm_raw,'source/trace-equation.json':trace_raw}
 for target,path in [
  ('source/TRACE13_PROOF.md',TRACE/'source/proofs/TRACE13_PROOF.md'),
  ('source/TRACE_SOURCE_PINS.json',TRACE/'SOURCE_PINS.json'),
  ('source/trace-coefficient-binding.json',TRACE/'source/inherited/root_fusion/coefficients/BINDING.json'),
  ('source/SIGNED_QUADRATIC_PROOF.md',PREFIX/'source/ordinary-proof.md'),
  ('source/RESIDUE_AND_DETERMINANT.md',PREFIX/'source/RESIDUE_AND_DETERMINANT.md'),
  ('source/independent_norm_oracle.py',PREFIX/'source/independent_norm_oracle.py'),
  ('source/prefix-check.json',PREFIX/'CHECK.json'),
  ('source/trace-check.json',TRACE/'CHECKS.json'),
  ('source/trace-degree.json',TRACE/'DEGREE.json'),
  ('source/signed-peer.md',PREFIX/'source/proof-peer.md'),
  ('source/signed-peer.json',PREFIX/'source/proof-peer.json'),
  ('source/LICENSE',PREFIX/'source/parent/LICENSE'),
  ('coefficients/BINDING.json',PREFIX/'coefficients/BINDING.json'),
 ]:files[target]=path.read_bytes()
 binding=json.loads(files['coefficients/BINDING.json'])
 for pin in binding['payloads'].values():
  rel='coefficients/'+pin['file'];files[rel]=(PREFIX/rel).read_bytes()
 files['CIRCUIT_BINDING.json']=encoded(dict(
  source_prefix_last=124,source_prefix_records=records,prefix_length=prefix_length,
  guard_rewrites=['Gv becomes G (drop v^2 multiplier)','guard+p1^2 becomes Ag (drop p1 variable)'],
  scaled_guard_child=E,norm_source_cutmap={str(i):j for i,j in cuts.items()},
  norm_source_node_map={str(i):j for i,j in sorted(fmap.items())},
  semantics='Full formula binding, not pointwise equality with either old endpoint. New unbounded zero-existence proof is PROOF.md.'))
 files['PROVENANCE.json']=encoded(dict(
  source_equation_sha256=PINS,generator_sha256=digest(Path(__file__).read_bytes()),
  source_file_sha256={p:digest(raw)for p,raw in files.items()if p.startswith('source/')},
  boundary='The ordinary inherited native/refutation theorem is composed only after restoring an old trace13 zero. No new Lean or internal-ZFC derivation.',
  authentic_coefficient_family='mixed-parity-unrounded-1064921',
  frozen_parents_unchanged=True))
 files['BUILD.json']=encoded(dict(status='PASS',integer_variables=13,operations=135,
  operation_counts=counts,exact_degree=536,
  sha256={name:digest(raw)for name,raw in files.items()}))
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
 for name,raw in build().items():
  path=OUT/name
  if a.check:need(path.read_bytes()==raw,'byte-identical '+name)
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
 print(json.dumps(dict(status='PASS',check=a.check,integer_variables=13,operations=135,exact_degree=536),indent=2))

if __name__=='__main__':main()
