#!/usr/bin/env python3
"""Further structural evidence: exact swap schema, block normal form, work counts.
This is independent Python analysis, not a formal proof or Rocq benchmark.
"""
from validation_guard import ensure_safe_runtime, read_pinned_source, read_pinned_source_bytes
ensure_safe_runtime()

from collections import Counter,defaultdict
from pathlib import Path
import hashlib,json
import prototype as p
import compare_flat_cfg as c
HERE=Path(__file__).resolve().parent

def block_normal_form(flat):
 t=flat['transitions'];test_ord={i:k for k,(i,row)in enumerate((i,row)for i,row in enumerate(t)if row[0]!='I')}
 def run(i):
  seen=set();count=Counter()
  while t[i][0]=='I':
   assert i not in seen,'increment-only cycle';seen.add(i)
   _,r,(j,)=t[i];count[r]+=1;i=j
  return tuple(sorted(count.items())),test_ord[i]
 rows=[]
 for i,(op,r,ss) in enumerate(t):
  if op=='I':continue
  rows.append((op,r,tuple(run(s)for s in ss)))
 return {'initial':run(flat['initial']),'rows':rows}

def owner(prog,path):
 nodes,n=prog
 for bit in path:
  o=n;op,r=nodes[n][bit]
  if op!='N':return o,int(bit),op,r
  n=r
 raise AssertionError('no leaf')

def instrumented(action):
 original=p.site;stats=defaultdict(lambda:{'calls':0,'node_edge_visits':0,'paths':Counter(),'sites':Counter()})
 def wrapper(prog,path):
  ans=original(prog,path);key='p215' if len(prog[0])==179 else 'dagPerm';s=stats[key]
  s['calls']+=1;s['node_edge_visits']+=len(ans[1]);s['paths'][path]+=1;s['sites'][ans[1]]+=1
  return ans
 p.site=wrapper
 try:action()
 finally:p.site=original
 return {k:{'calls':v['calls'],'node_edge_visits':v['node_edge_visits'],'distinct_input_paths':len(v['paths']),'distinct_canonical_leaf_sites':len(v['sites'])}for k,v in stats.items()}

def main():
 pa=p.read_prog('Prog215.v');pb=p.read_prog('DagPerm.v');a=c.flatten(pa);b=c.flatten(pb);ta=a['transitions'];tb=b['transitions']
 diff=[i for i,(x,y)in enumerate(zip(ta,tb))if x!=y];assert len(diff)%2==0
 pairs=[(diff[k],diff[k+1])for k in range(0,len(diff),2)]
 incoming=defaultdict(set)
 for i,(_,_,succ)in enumerate(ta):
  for j in succ:incoming[j].add(i)
 assert all(j==i+1 and ta[i][2]==(j,) and ta[i][1]==tb[j][1]and ta[j][1]==tb[i][1]for i,j in pairs)
 assert all(incoming[j]=={i}and a['initial']!=j for i,j in pairs)
 assert all(x[0]==y[0]and x[2]==y[2]for x,y in zip(ta,tb))
 locations=[{'first_ordinal':i,'second_ordinal':j,
   'p215_register_order':[ta[i][1],ta[j][1]],'dagPerm_register_order':[tb[i][1],tb[j][1]],
   'p215_paths':[''.join('1' if bit else '0' for bit in a['primitive'][k][0])for k in [i,j]],
   'dagPerm_paths':[''.join('1' if bit else '0' for bit in b['primitive'][k][0])for k in [i,j]],
   'first_successor':ta[i][2],'second_successors':ta[j][2],
   'second_predecessors':sorted(incoming[j]),'second_is_initial':a['initial']==j,
   'dagPerm_owner_node':owner(pb,b['primitive'][i][0])[0]}for i,j in pairs]
 (HERE/'cfg_swap_locations.json').write_text(json.dumps(locations,indent=2)+'\n')
 swapped=(list(pb[0]),pb[1])
 for n in [188,190]:swapped[0][n]=tuple(reversed(swapped[0][n]))
 swapped_flat=c.flatten(swapped)
 assert a['initial']==swapped_flat['initial'] and ta==swapped_flat['transitions']
 swapped_receipt={'status':'PASS_PYTHON_EXACT_ORDERED_CFG_EQUALITY_NOT_KERNEL',
   'changes':[{'node':188,'before':pb[0][188],'after':swapped[0][188]},
              {'node':190,'before':pb[0][190],'after':swapped[0][190]}],
   'changed_nodes_only':[188,190],'initial_ordinals':[a['initial'],swapped_flat['initial']],
   'ordered_primitives_and_all_successor_ordinals_equal':True,
   'expanded_occurrences_covered':len(pairs),'shared_node_contracts_needed':2,
   'locations_file':'cfg_swap_locations.json'}
 (HERE/'two_node_swap_result.json').write_text(json.dumps(swapped_receipt,indent=2)+'\n')
 schemas=Counter((ta[i][1],ta[j][1],tb[i][1],tb[j][1])for i,j in pairs)
 owner_schemas=Counter((owner(pa,a['primitive'][i][0]),owner(pa,a['primitive'][j][0]),owner(pb,b['primitive'][i][0]),owner(pb,b['primitive'][j][0]))for i,j in pairs)
 na=block_normal_form(a);nb=block_normal_form(b);assert na==nb
 block=json.dumps(na,separators=(',',':')).encode();(HERE/'common_block_cfg.json').write_bytes(block+b'\n')
 cert=p.read_cert();canonical_pairs=Counter((p.site(pa,u)[1],p.site(pb,v)[1])for u,v,_,_,_ in cert)
 successors=[0]
 for u,v,z,j,k in cert:
  if p.site(pa,u)[0][0]!='H':successors.extend([j,k])
 old_profile=instrumented(lambda:p.check(pa,pb,cert))
 flat_profile=instrumented(lambda:(c.flatten(pa),c.flatten(pb)))
 mutation_rejected=[]
 # Structural checker must distinguish test labels, branch targets, and increment bags.
 for tag,ordinal,replacement in [('change_test',0,('D',99,ta[0][2])),('change_target',0,(ta[0][0],ta[0][1],(0,0))),('change_increment',pairs[0][0],('I',99,ta[pairs[0][0]][2]))]:
  changed=dict(a);changed['transitions']=list(ta);changed['transitions'][ordinal]=replacement
  try:equal=block_normal_form(changed)==nb
  except (AssertionError,KeyError):equal=False
  assert not equal;mutation_rejected.append(tag)
 result={'status':'PASS_PYTHON_CFG_NORMAL_FORM_NOT_KERNEL_CHECKED','ordered_cfg_equal':False,
   'all_primitive_kinds_equal':True,'all_successor_ordinals_equal':True,
   'primitive_occurrences_per_program':len(ta),'symbolically_reachable_occurrences_per_program':len(a['bfs']),
   'different_increment_ordinals':len(diff),'adjacent_swap_pairs':len(pairs),
   'swap_schemas':[{'p215':list(k[:2]),'dagPerm':list(k[2:]),'instances':v}for k,v in schemas.items()],
   'shared_dag_swap_owner_schemas':[{'p215_first':k[0],'p215_second':k[1],'dagPerm_first':k[2],'dagPerm_second':k[3],'instances':v}for k,v in owner_schemas.items()],
   'all_pair_interiors_have_only_first_as_predecessor':True,
   'all_pair_interiors_not_initial':True,'normalized_block_cfgs_equal':True,
   'normalized_cfg_test_halt_rows':len(na['rows']),
   'normalized_cfg_edges_plus_initial':sum(len(row[2])for row in na['rows'])+1,
   'common_cfg_json_bytes':len(block)+1,'common_cfg_sha256':hashlib.sha256(block+b'\n').hexdigest(),
   'old_certificate_rows':len(cert),'old_rows_after_leaf_site_canonicalization':len(canonical_pairs),
   'redundant_checkpoint_rows_after_canonicalization':len(cert)-len(canonical_pairs),
   'old_branch_lookups_per_direction':len(successors),
   'old_linear_certificate_list_cell_visits_per_direction':sum(j+1 for j in successors),
   'old_max_certificate_index':max(successors),
   'old_one_direction_python_semantics_profile':old_profile,
   'new_two_program_flatten_python_semantics_profile':flat_profile,
   'mutation_checks_rejected':mutation_rejected,
   'counting_note':'List-cell visits count j+1 destructs for each successful nth_error lookup at index j in the literal checker; excludes VM sharing/compiler optimizations. Site profiles count Python semantic operations, not Rocq runtime benchmarks.',
   'verification_boundary':'No compiler or kernel execution. A generic epsilon-elimination/source-to-CFG theorem, increment commutation/block-sum theorem, and kernel evaluation against the literal programs remain necessary.'}
 (HERE/'cfg_rewrite_result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
