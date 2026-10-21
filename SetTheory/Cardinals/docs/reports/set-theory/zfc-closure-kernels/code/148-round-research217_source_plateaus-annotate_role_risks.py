"""Owned source-only hazard annotation. No physical allocation claim."""
import search_plateaus as S
import json
summary=json.load(open(S.OUT/'SUMMARY.json'));out=[]
for rec in summary['source_candidates']:
 root=S.root;changes=[]
 for step in rec['rotations']:
  target=next(n for n in S.nodes(root)if S.digests[n]==step['node_merkle_sha256'])
  direction,factors,replacement=next(x for x in S.rotations(target)if x[0]==step['direction'])
  assert S.digests[replacement]==step['replacement_merkle_sha256']
  changes.append(dict(direction=direction,target_baseline_states=S.baseqs.get(target,[]),target_merkle_sha256=S.digests[target],replacement_children=[dict(kind='primitive'if S.terms[c][0]=='L'else'internal',leaves=S.sizes[c],baseline_entries=S.baseqs.get(c,[]),primitive=list(S.terms[c][1:])if S.terms[c][0]=='L'else None)for c in S.terms[replacement][1:]]))
  root=S.change(root,target,replacement)
 assert S.digests[root]==rec['root_merkle_sha256']
 gone=S.base-S.nodes(root);affected={q for n in gone for q in S.baseqs.get(n,[])};helpers=sorted(affected&S.known_helpers)
 out.append(dict(source_file=rec['source_file'],source_sha256=rec['source_sha256'],ast_sha256=rec['ast_sha256'],rotations=changes,removed_baseline_source_roles=sorted(affected),known_selector_helper_states_with_changed_source_role=helpers,shared_decoder_states_with_changed_source_role=sorted(q for q in affected if len(S.groups[q])>1),physical_scope='A removed baseline source role is not a removable physical state. Row reuse needs all arithmetic, bootstrap, decoder, and selector contracts. No row changes are authorized by this annotation.'))
S.dump('ROLE_RISK_ANNOTATIONS.json',out)
print('annotated',len(out),'one_step_helper_unchanged',sum(len(x['rotations'])==1 and not x['known_selector_helper_states_with_changed_source_role']for x in out))
for x in out:
 if len(x['rotations'])==1 and x['rotations'][0]['target_baseline_states'] in([86],[188],[85]):print(json.dumps(x))
