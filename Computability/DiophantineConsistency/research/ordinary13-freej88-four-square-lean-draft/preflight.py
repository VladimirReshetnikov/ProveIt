#!/usr/bin/env python3
"""Read-only, source-level preflight; no Lean invocation or build approval."""
import hashlib, json, re, shutil
from pathlib import Path
here = Path(__file__).resolve().parent
root = here.parents[1]
pins = {
 'research/ordinary13-four-square88-30/candidate.json': 'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420',
 'reviews/ordinary13-four-square88-30-independent/check.py': '0883709a84091c0c6ff099bbf39bb9a60bf9a3f4cff7433f83a2718ade027167',
 'reviews/ordinary13-four-square88-30-independent/result.json': '50ff79fdffe3b91724b8da9f5dad19ffb5a14bcaf4cf57737b4db29366048f86',
 'research/ordinary13-ordinary-pair88-46/freej88.json': 'fc4627a15edc10f4cfcd3e6acf7df0896bb552a5f00cf238af6f1b5a349975bb',
 'research/ordinary13-freej88-lean-draft/P88PairGraph.lean': 'a792a7731d88b61483f34bf6fea4ef46a983d7e95b19cf9f891f622691ac49f2',
 'research/ordinary13-freej88-lean-draft/P88PairModel.lean': '21d468a34cf1dfc8df9b2fa4e4ad359294a1047f28ac3aec39bb4f2cc054001a',
 'reviews/ordinary13-freej88-lean-draft-independent/check.py': '835b1ff7ed2c051588cd0fe684948f7bc4701adccdafbd717d5ecff6818ee7ac',
 'reviews/ordinary13-freej88-lean-draft-independent/result.json': '598572932ccb239c860aa4cf865ff02c76f4cf317a84d563b5cca9b70d64efb5',
 'research/ordinary13-freej88-provider-survey/inspect.py': '08fea8f7be3d0ac22e59bcf7265b5b023a2e1ede4a89c0d062c50fdce359e8ab',
 'research/ordinary13-freej88-provider-survey/observation.json': 'ff8c85cefd57297ed6fcec7da1a8fbc7f53e777506464e7aed53060f7eeba024',
 'reviews/ordinary13-freej88-provider-survey-independent/check.py': 'd96eb20d3304d7d52e414d5a2697bafbb30553fd197f00dc7802ea1807beedd1',
 'reviews/ordinary13-freej88-provider-survey-independent/result.json': '1eeb89e3bd869a6804ff718b76a9ff6a39b7cf7dc1e4ba2aafe489fd6eddef60',
}
draft_pins = {
 'P88FourSquareGraph.lean': '614cb3ed5a91e919b5e44a5ae7f4fa7210a0a8b41bf5953d99d54c303b4f042e',
 'P88FourSquareModel.lean': '1fb9d7a6d1b906c87877c3146787c5fea5558f2473aac029b7be702763df7192',
 'P88FourSquareEndpoint.lean': '73260f5641e2d2d177e86d87e03af2e8dbcd8ef8b3829cc0cb55703dbaad07f9',
}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
for name, expected in pins.items(): assert sha(root / name) == expected, name
for name, expected in draft_pins.items(): assert sha(here / name) == expected, name
new = json.loads((root / 'research/ordinary13-four-square88-30/candidate.json').read_text())
old = json.loads((root / 'research/ordinary13-ordinary-pair88-46/freej88.json').read_text())
assert new['parent_sha256'] == pins['research/ordinary13-ordinary-pair88-46/freej88.json']
assert len(new['source']) == len(old['source']) == 88
assert new['witnesses'] == old['witnesses'] and new['fixed_numerals'] == old['fixed_numerals']
source = (here / 'P88FourSquareGraph.lean').read_text()
body = source.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
pat = re.compile(r'^  let (\w+) := (\w+|[0-9]+) ([+*\-]) (\w+|[0-9]+)$')
def atom(x): return int(x) if x.isdecimal() else x
rows = []
for line in body.splitlines():
    m = pat.fullmatch(line); assert m, line
    n,a,op,b = m.groups(); rows.append([n,op,atom(a),atom(b)])
assert rows == new['source']
for i,n in enumerate(new['witnesses']): assert f'  let {n} : Expr (Fin 13) := .var {i}' in source
for i,n in enumerate(new['fixed_numerals']): assert f'  let {n} : Expr (Fin 13) := .constant (p {i})' in source
assert '  ⟨A0, A1, Fa, g72, out⟩' in source
assert json.loads((root/'reviews/ordinary13-four-square88-30-independent/result.json').read_text())['status'] == 'PASS_SCOPED_INDEPENDENT_REVIEW'
assert json.loads((root/'reviews/ordinary13-freej88-provider-survey-independent/result.json').read_text())['status'] == 'PASS_READ_ONLY_INDEPENDENT_REVIEW'
free = shutil.disk_usage('/tmp').free
print(json.dumps({'status':'SOURCE_ONLY_NOT_LAUNCH_APPROVAL', 'pinned_paths':len(pins)+len(draft_pins),
 'literal_rows':len(rows), 'coordinates':13, 'arbitrary_integer_ports':4,
 'candidate_parent_pin':'PASS', 'tmp_free_bytes':free, 'disk_stop_bytes':5100000000,
 'disk_above_stop_at_sample':free>5100000000,
 'lean_status':'UNCOMPILED: requires authenticated providers, independently reviewed guard, adequate disk and allocated Lean slot',
 'scope':'Point-in-time pins and source parsing only; no Lean, build readiness, signed-integer Lean theorem, exact-degree theorem or file binding.'},indent=2,sort_keys=True))
