#!/usr/bin/env python3
"""Read-only source/point-provider survey. Never starts Lean or approves a run."""
import hashlib
import json
import re
import shutil
from pathlib import Path

HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
WORKTREE=HERE.parents[3]
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105')
pins={
  'candidate':(PROJECT/'research/ordinary13-ordinary-pair88-46/freej88.json','fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb'),
  'candidate_audit':(PROJECT/'reviews/ordinary13-ordinary-pair88-46-independent/check.py','8d4629946284f383d149fe00b631ced0f3ec957f9ca9bff1880d8090ca42e74b'),
  'candidate_audit_result':(PROJECT/'reviews/ordinary13-ordinary-pair88-46-independent/result.json','a571586752a404a816cc34f6eeba5e7b372eca9ce2cec9b4c19ec031d02fdae8'),
  'FreeJ13':(PROJECT/'Lean/DiophantineConsistency/Compact44/FreeJ13.lean','cf8beb3993b1cd716266d7adf06ab9ee4eda5d5a7e4b921072eecc5b31389d01'),
  'FreeJ13Halt':(PROJECT/'Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean','18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a'),
  'IPRAOrdinary13':(PROJECT/'Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean','c6b54e6098062be18966a9fd5891284909bd1454d6d6ee8b0db26e808045a735'),
  'provider_observation':(PROJECT/'research/ordinary13-p73-provider-preflight/observation.json','f37f6add7288d06a4e1ba60b97bc0ea5c00eeac13c5372bdceea4174c88bdae5'),
  'provider_audit':(PROJECT/'reviews/ordinary13-p73-provider-preflight-independent/check.py','e7cc82dccb993320b72af7a5665013c8e96ff45ef649d5b5ee74150295fbcf5a'),
  'provider_audit_result':(PROJECT/'reviews/ordinary13-p73-provider-preflight-independent/result.json','fc29d005ab3597cad866219fb8bdfe8f4495743ad3215cd02732c8933140480c'),
  'P88PairGraph.lean':(HERE/'P88PairGraph.lean','a792a7731d88b61483f34bf6fea4ef46a983d7e95b19cf9f891f622691ac49f2'),
  'P88PairModel.lean':(HERE/'P88PairModel.lean','21d468a34cf1dfc8df9b2fa4e4ad359294a1047f28ac3aec39bb4f2cc054001a'),
  'P88PairEndpoint.lean':(HERE/'P88PairEndpoint.lean','41682e57745920cfbe57e6198db41312976b7722f329c2b989a1e98d3d41eebf'),
  'make_graph.py':(HERE/'make_graph.py','06545ce2a9d19a36b25d42f1b0a1d926fedb8dbdd500386436c173aa81eb966d'),
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for label,(path,expected) in pins.items():
    assert path.is_file() and sha(path)==expected, label
assert json.loads(pins['candidate_audit_result'][0].read_text())['status']=='PASS_SCOPED_INDEPENDENT_REVIEW'
assert json.loads(pins['provider_audit_result'][0].read_text())['status']=='PASS_READ_ONLY_INDEPENDENT_REVIEW'
graph=json.loads(pins['candidate'][0].read_text())
lean=pins['P88PairGraph.lean'][0].read_text()
block=lean.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
pat=re.compile(r'^  let (\w+) := (\w+|[0-9]+) ([+*\-]) (\w+|[0-9]+)$')
def atom(s):return int(s) if s.isdecimal() else s
rows=[]
for line in block.splitlines():
    m=pat.fullmatch(line);assert m,line
    name,left,op,right=m.groups();rows.append([name,op,atom(left),atom(right)])
assert len(rows)==88 and rows==graph['source']
for i,name in enumerate(graph['witnesses']):
    assert f'  let {name} : Expr (Fin 13) := .var {i}' in lean
for i,name in enumerate(graph['fixed_numerals']):
    assert f'  let {name} : Expr (Fin 13) := .constant (p {i})' in lean
assert '  ⟨A0, A1, Fa, Fs, out⟩' in lean

prior=json.loads(pins['provider_observation'][0].read_text())
assert not prior['recorded_route_issues'] and not prior['source_head_issues']
front=prior['endpoint']['p72_frontier']
shorts=('FreeJSumSquares','FreeJSignedTransport','FreeJGraphAuxiliary','QCube92Halt','IPRAOrdinary12Chain')
frontier={}
for short in shorts:
    name='DiophantineConsistency.Compact44.'+short
    assert name in front
    obj=P72/'lib'/Path(name.replace('.','/')+'.olean')
    frontier[name]={'exists':obj.is_file(), 'matches_prior_point_hash':obj.is_file() and sha(obj)==front[name]['object_sha256'],
                    'expected_sha256':front[name]['object_sha256']}
build=WORKTREE/'.lake/build/lib/lean/DiophantineConsistency/Compact44'
missing_candidates={n:{'p72':(P72/'lib/DiophantineConsistency/Compact44'/(n+'.olean')).is_file(),
                       'project_build':(build/(n+'.olean')).is_file()}
                    for n in ('FreeJ13','FreeJ13Halt','IPRAOrdinary13')}
free=shutil.disk_usage('/tmp').free
print(json.dumps({'status':'READ_ONLY_OBSERVATION_NOT_LAUNCH_APPROVAL',
  'source_pins':'PASS','literal_graph_rows_match':len(rows),'witnesses':len(graph['witnesses']),
  'integer_ports':graph['fixed_numerals'],'p72_frontier_point_observations':frontier,
  'parent_object_observations':missing_candidates,'tmp_free_bytes':free,'disk_stop_bytes':5100000000,
  'disk_above_stop_at_sample':free>5100000000,
  'launch_readiness':'BLOCKED: provider closure and guarded runner not freshly authenticated/reviewed',
  'scope':'Read-only point survey, not compilation, all-signed-integer Lean proof, complete package/dynamic ancestry, or file semantics.'
},indent=2,sort_keys=True))
