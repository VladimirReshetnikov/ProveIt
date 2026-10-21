"""Owned local row-plan ranking of SAVED sources, not a physical census.
No new AST candidates, machines, or primitive proofs are generated.
"""
import search_plateaus as S
from collections import defaultdict,Counter
import json
records=json.load(open(S.OUT/'SUMMARY.json'))['source_candidates']
near=json.load(open(S.ROOT/'research217_encoding/TWO_CELL_SELECTOR_SCREEN.json'))['near_matches']
blocked={(q,b)for q in(85,157,200)for b in(0,1)}|{(188,1),(189,1),(190,0),(190,1),(156,1),(176,1)}
# Literal existing direct leaf entry actions; these remain interface obligations.
actions=defaultdict(set)
for op,b,act,p in S.gates:
 if act[:2]==(b,1):actions[op,b].add(act)

class Reject(Exception):pass
def plan(rec):
 root=S.root;mapping={n:set(qs)for n,qs in S.baseqs.items()};table=S.T.copy();steps=[]
 for step in rec['rotations']:
  target=next(n for n in S.nodes(root)if S.digests[n]==step['node_merkle_sha256'])
  direction,factors,replacement=next(x for x in S.rotations(target)if x[0]==step['direction'])
  assert S.digests[replacement]==step['replacement_merkle_sha256']
  nr=S.change(root,target,replacement);live=S.nodes(nr);now=S.nodes(root)
  targetqs=mapping.get(target,set())
  if len(targetqs)!=1:raise Reject('ambiguous_target_entry')
  q=next(iter(targetqs));qroles={n for n,qs in mapping.items()if q in qs and n in now}
  if qroles!={target}:raise Reject('target_has_multiple_source_roles')
  oldinner=S.terms[target][1 if direction=='right'else 2];newinner=S.terms[replacement][2 if direction=='right'else 1]
  eq=mapping.get(newinner,set());reused=None
  if eq:
   if len(eq)!=1:raise Reject('ambiguous_existing_inner_entry')
   innerq=next(iter(eq));existing=True
  else:
   oq=mapping.get(oldinner,set())
   if oldinner in live or len(oq)!=1:raise Reject('new_inner_has_no_unambiguous_extinct_slot')
   innerq=next(iter(oq));roles={n for n,qs in mapping.items()if innerq in qs and n in now}
   if roles!={oldinner}:raise Reject('old_inner_slot_has_multiple_source_roles')
   reused=innerq;existing=False
  def act(child,b):
   if S.terms[child][0]=='L':
    op=tuple(S.terms[child][1:]);alts=actions[op,b]
    if len(alts)!=1:raise Reject('primitive_interface_not_unique_direct')
    return next(iter(alts))
   if child==newinner:z=innerq
   else:
    qs=mapping.get(child,set())
    if len(qs)!=1:raise Reject('child_entry_not_unique')
    z=next(iter(qs))
   return b,1,z
  patch={(q,b):act(c,b)for b,c in enumerate(S.terms[replacement][1:])}
  if not existing:patch.update({(innerq,b):act(c,b)for b,c in enumerate(S.terms[newinner][1:])})
  changes={row:a for row,a in patch.items()if table[row]!=a}
  if set(changes)&blocked:raise Reject('reserved_or_selector_helper_row')
  table.update(changes)
  newmap=defaultdict(set)
  for n,qs in mapping.items():
   if n in now:newmap[S.change(n,target,replacement)].update(qs)
  newmap[newinner].add(innerq)
  mapping={n:qs for n,qs in newmap.items()if n in live}
  steps.append(dict(target_state=q,direction=direction,inner_state=innerq,reused_extinct_inner_state=reused,existing_inner_entry=existing,local_changed_rows=[list(r)for r in sorted(changes)]))
  root=nr
 assert S.digests[root]==rec['root_merkle_sha256']
 delta=[dict(row=list(row),old=list(S.T[row]),new=list(a))for row,a in sorted(table.items())if S.T[row]!=a]
 changed={tuple(x['row'])for x in delta};selector=[]
 for i,n in enumerate(near):
  key=(n['missing_role'],n['read']);old=S.T[key];new=table[key]
  alltrace=n['wrong_trace']+n['matching_trace'];used={(x[0],x[2])for x in alltrace}
  if old[:2]==new[:2] and new[2]==n['actual_target']and not changed&used:
   selector.append(dict(near_index=i,kind='old_missing_role_endpoint_now_matches_unchanged_helper',pair=n['pair'],row=list(key),old_target=old[2],new_target=new[2],action=n['action']))
  # Endpoint-only replacement on the last wrong trace row, with all prior
  # trace rows and matching marker branch unchanged.
  tr=n['wrong_trace']
  if tr:
   last=tr[-1];key2=(last[0],last[2]);before={(x[0],x[2])for x in tr[:-1]+n['matching_trace']}
   if key2 in changed and not changed&before and table[key2][:2]==S.T[key2][:2] and table[key2][2]==new[2] and table[key2][2]==n['expected_target']:
    selector.append(dict(near_index=i,kind='wrong_helper_final_target_now_matches',pair=n['pair'],row=list(key2),old_target=S.T[key2][2],new_target=table[key2][2],action=n['action']))
 return dict(source_file=rec['source_file'],source_sha256=rec['source_sha256'],ast_sha256=rec['ast_sha256'],dag_nodes=205,steps=steps,changed_rows=delta,changed_row_count=len(delta),displaced_physical_role_count=len({r[0]for r in changed}),existing_inner_reuses=sum(x['existing_inner_entry']for x in steps),selector_endpoint_leads=selector,scope='Local syntactic row plan only. Physical source binding, shared-child marker compatibility, all primitive/selector contracts and startup remain unproved. Not a machine or state-count claim.')

ranked=[];fail=Counter()
for r in records:
 try:ranked.append(plan(r))
 except Reject as e:fail[str(e)]+=1
ranked.sort(key=lambda x:(-bool(x['selector_endpoint_leads']),x['displaced_physical_role_count'],x['changed_row_count'],-x['existing_inner_reuses'],len(x['steps']),x['source_sha256']))
S.dump('PHYSICAL_LEAD_RANKING.json',dict(input_saved_sources=len(records),plans=len(ranked),excluded=dict(fail),protected_rows=[list(x)for x in sorted(blocked)],ranked=ranked))
print('PLANS',len(ranked),'excluded',dict(fail),'selector',sum(bool(x['selector_endpoint_leads'])for x in ranked))
for r in ranked[:10]:print(json.dumps(r))
