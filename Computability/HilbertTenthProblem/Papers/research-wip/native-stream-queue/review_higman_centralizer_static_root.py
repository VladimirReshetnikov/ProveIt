"""Original one-run inert-record audit; no group words are evaluated."""
import hashlib
import json
from pathlib import Path

TMP = Path('/tmp')
OUT = TMP / 'review_higman_centralizer_static_root.json'
assert not OUT.exists(), 'Never replay a frozen first audit.'
PINS = {
    'positive7_higman_literal_presentation_riemann.json': '35a24f7ff3878f132e9bb37fa76a0c21de31795c2f72ea9e497c5efb7d1c1a57',
    'review_positive7_higman_literal_static_pascal.json': '39f3d7a0eaeb5568da89b6188fac13f2cfbdbb462b4d8237359e7197a1b537eb',
    'positive7_higman_centralizer_branch_riemann.py': '53dd31030ccf68f604b47fb6157a81f7472b96eed766b07be308ae40dfe29516',
    'positive7_higman_centralizer_branch_riemann.json': '78ea459d083b1b65aa7c7d79f2af95f0bf9262d5db8bce83e08396340709869b',
    'positive7_higman_membership_word_problem_aristotle.md': '964fb2bedf08cb5ff2c985076baeaf30235baf17e8169611cd809244d9f7d709',
}
raws = {}
for filename, pin in PINS.items():
    data = (TMP / filename).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin, filename
    raws[filename] = data


def record_sha(value):
    return hashlib.sha256(json.dumps(value, separators=(',', ':'), ensure_ascii=True).encode()).hexdigest()


parent = json.loads(raws['positive7_higman_literal_presentation_riemann.json'])
prior_audit = json.loads(raws['review_positive7_higman_literal_static_pascal.json'])
assert prior_audit['status'] == 'PASS:499 generators,17678 literal relators,124 traces,123 caches,3 final words'
branch = json.loads(raws['positive7_higman_centralizer_branch_riemann.json'])
assert set(branch) == {'schema','scope','source','parent','mathematical_premise','generators','relators',
                       'event_catalog','marker_ids','Accepted_words','query_ports','query_family',
                       'word_conventions','census','boundaries','status'}
assert branch['schema'] == 'positive7-Accepted-centralizer-literal-v1'
assert branch['scope'] == 'Direct identity-HNN word-problem branch; no two-generator or arithmetic-interface expansion.'
assert branch['generators'][:498] == parent['generators'][:498]
assert branch['relators'][:17676] == parent['relators'][:17676]
assert branch['generators'][498:] == [{'id':499,'name':'centralizer/t','event':124,'declared_after_relator':17676}]
expected_added = []
for slot, marker in enumerate((467,468,469)):
    ell = [-498,-497,marker,497,498]
    expected_added.append({'index':17676+slot,'event':124,'family':'centralizer/fix/'+str(slot),
                          'stable':[499],'source':ell,'target':ell,
                          'word':[-499,-498,-497,marker,497,498,499,-498,-497,-marker,497,498]})
assert branch['relators'][17676:] == expected_added
assert branch['marker_ids'] == [467,468,469]
assert branch['Accepted_words'] == [r['source'] for r in expected_added]
assert branch['Accepted_words'] == parent['trace'][122]['created_lists']['Accepted']
assert branch['query_ports'] == {'alpha':[-468]*23+[467]+[468]*23,'beta':[-469,468,469],'t':[499]}

catalog = []
for event in parent['trace'][:123]:
    item = {key:event[key] for key in ('id','label','kind','new_generator_ids','relator_interval')}
    item['parent_event_sha256'] = record_sha(event)
    catalog.append(item)
catalog.append({'id':124,'label':'centralizer','kind':'identity_HNN_on_Accepted',
                'new_generator_ids':[499],'relator_interval':[17676,17679]})
assert branch['event_catalog'] == catalog
assert [r['id'] for r in branch['generators']] == list(range(1,500))
assert [r['index'] for r in branch['relators']] == list(range(17679))
assert len({r['name'] for r in branch['generators']}) == 499
assert branch['parent'] == {
    'path':str(TMP/'positive7_higman_literal_presentation_riemann.json'),
    'sha256':PINS['positive7_higman_literal_presentation_riemann.json'],
    'bytes':len(raws['positive7_higman_literal_presentation_riemann.json']),
    'prefix_generator_interval':[0,498],'prefix_relator_interval':[0,17676],
    'prefix_generators_sha256':record_sha(parent['generators'][:498]),
    'prefix_relators_sha256':record_sha(parent['relators'][:17676]),
    'prefix_trace_interval':[0,123],'prefix_trace_sha256':record_sha(parent['trace'][:123]),
    'Accepted_event_sha256':record_sha(parent['trace'][122]),
    'omitted_tail_generator_interval':[498,499],'omitted_tail_relator_interval':[17676,17678],
    'record_retention':'Every retained generator/relator object equals the exact parent slice.'}
for key, filename in [('source','positive7_higman_centralizer_branch_riemann.py'),
                       ('mathematical_premise','positive7_higman_membership_word_problem_aristotle.md')]:
    pathkey = 'path_at_first_run' if key == 'source' else 'path'
    assert branch[key] == {pathkey:str(TMP/filename),'sha256':PINS[filename],
                           'bytes':len(raws[filename]),'LF_lines':raws[filename].count(b'\n')}
assert branch['query_family'] == {
    'parameter':'ordinary integer n, not instantiated by this composer',
    'h_n':'inverse(beta^n) alpha beta^n','W_n':'inverse(h_n) inverse(t) h_n t',
    'claim':'W_n=1 in the presented group iff n belongs to the fixed universal set U',
    'status':'symbolic word notation only, justified by the separately pinned HNN/free-basis proof'}
assert branch['word_conventions'] == {'letters':'flat signed generator IDs; no reduction',
    'fix_relation':'inverse(t) ell_i t inverse(ell_i)','commutator':'[h,t]=inverse(h) inverse(t) h t'}
assert branch['census'] == {'generators':499,'relators':17679,'inherited_generators':498,
    'inherited_relators':17676,'new_generators':1,'new_relators':3,'Accepted_words':3,
    'new_relation_lengths':[12,12,12],'fixed_query_port_lengths':{'alpha':47,'beta':3,'t':1}}
assert branch['boundaries'] == [
    'The original X_U output is unchanged; this is a separate branch from Accepted.',
    'Only the three Accepted words are centralized, not all ambient generators.',
    'No parameter query is instantiated or evaluated.',
    'No inherited X_U cache, final-state, selected-list or transducer metadata is active.',
    'The faithful two-generator/matrix/paid arithmetic interface remains open.']
assert branch['status'] == 'first original inert-prefix/literal-suffix composition; independent review separate'
report = {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'bindings':[{'filename':name,'sha256':pin,'bytes':len(raws[name])} for name,pin in PINS.items()],
          'scope':'All498 retained generator and17676 retained relator records; all new records and every top-level metadata field.',
          'new_records':expected_added,'query_ports':branch['query_ports'],'census':branch['census'],
          'group_word_evaluation':False,'parameter_evaluation':False,'prior_program_replayed':False,
          'parent_prefix_semantics':'Inherited through full independent Pascal literal audit and scoped mathematical premises.'}
with OUT.open('x') as stream:
    json.dump(report,stream,indent=2)
    stream.write('\n')
print('PASS: exact498/17676 prefix, three centralizer relations, all query ports and metadata')
