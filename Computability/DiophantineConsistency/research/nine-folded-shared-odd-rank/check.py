#!/usr/bin/env python3
"""Independent whole-node and polynomial identity for stored odd-rank sharing."""
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
PARENT=HERE.parent/'nine-folded-minimal-reflection'
OPS={'add','sub','mul'}
spec=importlib.util.spec_from_file_location('accepted_minimal_reflection_checker',PARENT/'check.py')
accepted=importlib.util.module_from_spec(spec);spec.loader.exec_module(accepted)
frozen,algebra,need=accepted.frozen,accepted.algebra,accepted.need

def digest(raw):return sha256(raw).hexdigest()
def load(p):return json.loads(p.read_bytes())

def sealed(path):
 m=path/'MANIFEST.json';pins=load(m);pins=pins.get('files',pins)
 need({str(p.relative_to(path))for p in path.rglob('*')if p.is_file()and p!=m}==set(pins),'whole closed packet '+str(path))
 for name,pin in pins.items():need(digest((path/name).read_bytes())==pin,'whole sealed member '+name)

def local_check(parent,g,expected):
 receipt=algebra.topology(g,expected);old,nodes=parent['nodes'],g['nodes'];labels=parent['named_nodes']
 B1=labels['B1'];node=old[B1];need(node['kind']=='add','actual parentB1 addition')
 one,twice=node['left'],node['right'];need(old[one]==dict(kind='literal',value=1),'literalone in oddrank')
 need(old[twice]['kind']=='mul','actual private twiceR gate');two,R=old[twice]['left'],old[twice]['right']
 need(old[two]==dict(kind='literal',value=2),'actual scalar2')
 need(old[R]['kind']=='sub'and old[R]['right']==one,'actual source rank subtraction');rp1=old[R]['left']
 consumers=[j for j,n in enumerate(old)if n['kind']in OPS and twice in[n['left'],n['right']]]
 need(consumers==[B1],'whole private2R consumer boundary')
 mapping={int(i):j for i,j in g['parent_clone_map'].items()}
 need(g['deleted_parent_nodes']==[twice]and g['changed_parent_nodes']==[B1]and g['inserted_child_nodes']==[],'allandonly declared rewrite nodes')
 need(set(mapping)==set(range(len(old)))-{twice}and set(mapping.values())==set(range(len(nodes)))and len(set(mapping.values()))==len(mapping),'every parent/child node accounted exactlyonce')
 for i,j in mapping.items():
  if i==B1:continue
  n=dict(old[i])
  if n['kind']in OPS:n.update(left=mapping[n['left']],right=mapping[n['right']])
  need(n==nodes[j],'all retained literal operations/operands/leaves')
 need(nodes[mapping[B1]]==dict(kind='add',left=mapping[R],right=mapping[rp1]),'exact newshared oddrank operands')
 need(set(g['named_nodes'])==set(labels)|{'sourceRank','sourceRankPlusOne'},'complete namedregister inventory')
 for label,index in labels.items():need(g['named_nodes'][label]==mapping[index],'every namedcut retained')
 need(g['named_nodes']['sourceRank']==mapping[R]and g['named_nodes']['sourceRankPlusOne']==mapping[rp1],'actual shared source register binding')
 for field in ['variables','domain','coefficient_recipes','fixed_binding','coherent_tuple','source_snapshot','base_scale_exponent',
               'threshold_scale_exponent','source_degree','threshold_degree','A_degree','W']:
  need(g[field]==parent[field],'complete unchanged source binding '+field)
 need(g['output']==mapping[parent['output']],'same whole output schedule')
 before,seen_before=frozen.normal_form(dict(parent,output=B1),{rp1:'rankPlusOne'})
 after,seen_after=frozen.normal_form(dict(g,output=mapping[B1]),{mapping[rp1]:'rankPlusOne'})
 rp=algebra.atom('rankPlusOne');want=algebra.sub(algebra.times(2,rp),algebra.const(1))
 need(before==after==want,'allcoefficients of actual complete B1 identity over freeRankPlusOne')
 T,O,a,I=[algebra.atom(n)for n in['T','O','a','I']]
 wantnorm=algebra.sub(algebra.sq(algebra.add(algebra.sq(T),algebra.mul(algebra.sq(O),algebra.sub(a,I)))),
  algebra.times(4,algebra.mul(algebra.mul(algebra.sq(O),a),algebra.sq(T))))
 names=g['named_nodes'];norm,_=frozen.normal_form(g,{names['Theta']:'T',names['Omega']:'O',names['Ac']:'a',names['I']:'I'})
 need(norm==wantnorm,'every coefficient of complete two-root norm')
 degrees=[]
 for n in nodes:
  k=n['kind'];degrees.append(1 if k=='variable'else 0 if k in['literal','fixed']else
   degrees[n['left']]+degrees[n['right']]if k=='mul'else max(degrees[n['left']],degrees[n['right']]))
 need(all(degrees[g['named_nodes'][n]]==d for n,d in g['named_degrees'].items()),'all actual stored nameddegree metadata')
 receipt.update(all_parent_nodes_accounted=True,private_deleted_node=twice,changed_parent_B1=B1,
  source_R=R,source_RankPlusOne=rp1,all_coefficients_of_actual_rank_identity=True,
  pointwise_whole_polynomial_identity_by_schedule_induction=True)
 return receipt

def main():
 if(HERE/'MANIFEST.json').exists():sealed(HERE)
 sealed(PARENT);pins=load(HERE/'SOURCE_PINS.json')
 for path,pin in pins['retained_files'].items():need(digest((BASE/path).read_bytes())==pin,'complete pinned dependency '+path)
 need(pins['proof_sha256']==digest((HERE/'PROOF.md').read_bytes())and pins['generator_sha256']==digest((HERE/'build.py').read_bytes()),'current proof and generator pins')
 cases=[]
 with frozen.load_archive()as z:
  for name,count in[('boundary_simple',405),('compact_simple',413)]:
   parent=load(PARENT/(name+'.json'));g=load(HERE/(name+'.json'))
   need(g['parent_sha256']==digest((PARENT/(name+'.json')).read_bytes()),'whole immediateparentgraph')
   literal=local_check(parent,g,count);fixed,binding=frozen.fixed_values(z,'boundary'if name.startswith('boundary')else'compact',parent)
   degree=accepted.degree_witness(g,fixed);rejected=[]
   for label,change in[
    ('wrong_rank_operand',lambda b:b['nodes'][b['named_nodes']['B1']].__setitem__('right',b['named_nodes']['sourceRank'])),
    ('wrong_rank_sign',lambda b:b['nodes'][b['named_nodes']['B1']].__setitem__('kind','sub')),
    ('wrong_shared_register',lambda b:b['named_nodes'].__setitem__('sourceRankPlusOne',b['named_nodes']['sourceRank'])),
    ('norm_sign',lambda b:b['nodes'][b['output']].__setitem__('kind','add')),
    ('source_port',lambda b:next(n for n in b['nodes']if n['kind']=='fixed').__setitem__('name','wrong')),
    ('domain',lambda b:b.__setitem__('domain','natural integers'))]:
    bad=deepcopy(g);change(bad)
    try:local_check(parent,bad,count)
    except(ValueError,KeyError,IndexError):rejected.append(label)
    else:raise ValueError('accepted corruption '+label)
   cases.append(dict(name=name,literal=literal,degree=degree,whole_fixed_binding=binding,rejected_mutations=rejected))
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),cases=cases,
  complete_norm_defect_identities=algebra.identities(),pointwise_entire_polynomial_identity=True,
  proof_sha256=digest((HERE/'PROOF.md').read_bytes()),scope='Exact complete stored-polynomial rewrite with all fixedvalues and exact degree. Ordinary source/refutation equivalence inherited by the identical positive witnesses. No newLean/internal-ZFC claim.')
 (HERE/('CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json')).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
 print(json.dumps(report,indent=2,sort_keys=True))
if __name__=='__main__':main()
