"""Independent finite transformation audits; imports no polynomial producer."""
import copy
from check_network import require,poly,subst,add

def guard_step(before,bc,after,ac):
 rec=ac['unit_guard_substitution'];n=len(before['variables']);keep=rec['retained_input_indices'];rs=rec['records_pre_compaction'];ren={i:j for j,i in enumerate(keep)}
 require(rec['schema']=='anchored-unit-dummy-substitution-v1' and rec['input_variables']==n,'guard input metadata')
 require(keep==sorted(set(keep)) and len(keep)==len(after['variables']) and all(type(i)==int and 0<=i<n for i in keep),'guard compaction')
 gone=set(range(n))-set(keep);defs={};usedlogic=set()
 for r in rs:
  d,x,u,k=r['deleted_dummy'],r['anchor'],r['unit'],r['normalized_variable']
  require(d in gone and d not in defs and k not in usedlogic,'guard unique deleted dummy');usedlogic.add(k)
  require(before['variables'][d]=={'kind':'equality_dummy','normalized_variable':k},'guard genuine dummy')
  cy=next(z for z in bc['equality_cycles'] if z['normalized_variable']==k)
  require(cy.get('mode','cycle')=='cycle' and len(cy['aliases'])==3 and d in cy['aliases'],'guard old 3-cycle')
  ids=[i for i in cy['aliases'] if i!=d]
  require(x in ids and x in ren and u in ren and u in bc['unit_path'],'guard anchor and existing unit')
  require(all(before['variables'][i]=={'kind':'alias','normalized_variable':k} for i in ids),'guard two ordinary aliases')
  require(all(d not in e['monomial'] for e in bc['edges']) and d not in bc['unit_path'] and sum(d in z['aliases'] for z in bc['equality_cycles'])==1,'dummy occurs only in its own penalty')
  target=next(z for z in ac['equality_cycles'] if z['normalized_variable']==k)
  require(target=={'normalized_variable':k,'aliases':[ren[i] for i in ids],'mode':'unit_product_cycle','anchor':ren[x],'unit':ren[u]},'guard exact final relation')
  defs[d]={tuple(sorted([ren[x],ren[u]])):1}
 require(set(defs)==gone,'guard exactly all removed variables')
 require(after['variables']==[before['variables'][i] for i in keep],'guard retained coordinate metadata')
 maps=[{(ren[i],):1} if i in ren else defs[i] for i in range(n)]
 require(subst(poly(before['terms']),maps)==poly(after['terms']),'guard exact full literal substitution')
 return {'status':'pass','removed_dummies':len(gone),'exact_literal_substitution':True,'dummy_exclusivity':'checked','existing_anchored_units':'checked'}

def flow_step(before,bc,after,ac):
 r=ac['flow_contraction'];n=len(before['variables']);nv=len(bc['vertices']);keep=r['retained_input_indices'];kv=r['retained_input_vertices'];rs=r['records_pre_compaction']
 require(r['schema']=='internal-tree-flow-contraction-v1' and r['input_variables']==n and r['input_vertices']==nv,'flow input metadata')
 require(keep==sorted(set(keep)) and kv==sorted(set(kv)),'flow ordered compaction')
 current=poly(before['terms']);edges=copy.deepcopy(bc['edges']);parts=[bc['hub_vertices']]+bc['row_blocks'];owners={v:j for j,part in enumerate(parts) for v in part};deleted=set();dead=set()
 for step in rs:
  w,u,v=step['flow'],step['tail'],step['head'];require(w not in deleted and v not in dead and u not in dead and owners[u]==owners[v],'flow new internal contraction')
  found=[e for e in edges if e['kind']=='free' and e['monomial']==[w]];require(len(found)==1 and found[0]['tail']==u and found[0]['head']==v and found[0]['coefficient']==1,'flow exact tree edge')
  require(before['variables'][w]['kind']=='flow','flow deleted kind')
  restore={}
  for e in edges:
   if e is found[0]:continue
   sign=1 if e['tail']==v else -1 if e['head']==v else 0
   if sign:restore=add(restore,{tuple(sorted(e['monomial'])):sign*e['coefficient']})
  maps=[{(i,):1} for i in range(n)];maps[w]=restore;current=subst(current,maps)
  deleted.add(w);dead.add(v);edges.remove(found[0])
  for e in edges:
   for k in ['tail','head']:
    if e[k]==v:e[k]=u
 require(set(keep)==set(range(n))-deleted and set(kv)==set(range(nv))-dead,'flow exact retained namespaces')
 ren={i:j for j,i in enumerate(keep)};vr={i:j for j,i in enumerate(kv)}
 for e in edges:
  e['monomial']=[ren[i] for i in e['monomial']];e['tail']=vr[e['tail']];e['head']=vr[e['head']]
 require(edges==ac['edges'],'flow exact quotient edges')
 require(all(not deleted.intersection(m) for m in current),'flow eliminated symbolic coordinates')
 renamed={tuple(sorted(ren[i] for i in m)):z for m,z in current.items()}
 require(renamed==poly(after['terms']),'flow exact off-zero inverse substitution identity')
 require(after['variables']==[before['variables'][i] for i in keep] and ac['vertices']==[bc['vertices'][i] for i in kv],'flow retained metadata')
 require(ac['hub_vertices']==[vr[i] for i in bc['hub_vertices'] if i in vr] and ac['row_blocks']==[[vr[i] for i in b if i in vr] for b in bc['row_blocks']],'flow unchanged block ownership')
 return {'status':'pass','removed_flows':len(deleted),'exact_internal_tree_quotient':True,'exact_off_zero_inverse_substitution':True}
