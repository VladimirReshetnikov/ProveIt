#!/usr/bin/env python3
"""Check one import edit and both source-declared frontier changes, without Lean."""
from pathlib import Path
import collections,hashlib,json,re
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
OLD=TASK/'research/adaptive87-four-square-local-mod4-model-draft/FourUnitGeneric.lean.src'
RECEIPT=TASK/'research/adaptive87-four-square-local-mod4-model-draft/result.json'
SOURCE=TASK/'Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean'
NEW=HERE/'FourUnitGeneric.lean.src'
PINS={OLD:'697261314731a6c93c8910b4d030ea116f4058a8d30a76843bfc1bbaefd26569',
      RECEIPT:'84afb37c10d87b71240e0631b2288d1ee06efd46611efc79de8c17477c7fca08',
      SOURCE:'3870325628b4148b2825e1af96bbec91ecbb115e2e57a83d580df97ea53f07aa',
      NEW:'ab556dc8fec64126ee0c30fff512b3ffac8496dd561affa2cf39fbb59259591e'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in PINS.items():assert sha(p)==h,(p,sha(p))
s=OLD.read_text();a='import DiophantineConsistency.ModelCarrierScaled';b='import DiophantineConsistency.DiscreteOrderedRingFacts'
assert s.count(a)==1 and s.replace(a,b,1)==NEW.read_text()
discrete=SOURCE.read_text()
for pattern in [r'^def Discrete\b',r'^theorem eq_one_or_neg_one_of_mul_eq_one\b']:
 assert re.search(pattern,discrete,re.M),pattern
x=json.loads(RECEIPT.read_text());G=x['instantiated_endpoint_sources']
for row in G.values():assert sha(TASK/row['source'])==row['sha256'],row['source']
newimports=re.findall(r'^import\s+([\w.]+)$',NEW.read_text(),re.M)
H=dict(G);H['FourUnitGeneric']={'source':str(NEW.relative_to(TASK)),'sha256':sha(NEW),'imports':newimports}
def walk(graph,starts):
 q=collections.deque(starts);visited=set()
 while q:
  n=q.popleft()
  if n in visited:continue
  visited.add(n);q.extend(graph.get(n,{}).get('imports',[]))
 return visited
conditional=['FourSquare88Model'];instantiated=conditional+['DiophantineConsistency.HAAdaptiveFactor87']
records={}
for title,starts in [('conditional',conditional),('instantiated',instantiated)]:
 before=walk(G,starts);after=walk(H,starts)
 src=lambda xs:sorted(n for n in xs if n.startswith('DiophantineConsistency.') and n in H)
 removed=sorted(set(src(before))-set(src(after)));added=sorted(set(src(after))-set(src(before)))
 roots={'ha87':'/tmp/ha87-full-transitive-p3xt6wra/lib','current14':'/tmp/current14-standard-fresh-build-20261104/lib','peer':'/tmp/nine-ipra-guarded-peer-20261102-a/lib'}
 statuses={}
 for label,root in roots.items():
  present=[n for n in src(after) if (Path(root)/Path(*n.split('.')).with_suffix('.olean')).is_file()]
  statuses[label]={'present':len(present),'absent':len(src(after))-len(present)}
 records[title]={'before_project_sources':len(src(before)),'after_project_sources':len(src(after)),
  'removed_project_sources':removed,'added_project_sources':added,'factor_units_reachable':'DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011' in after,
  'carrier65_reachable':'DiophantineConsistency.Carrier65' in after,'model_carrier_scaled_reachable':'DiophantineConsistency.ModelCarrierScaled' in after,
  'sample_provider_presence':statuses}
assert not records['conditional']['factor_units_reachable']
assert records['instantiated']['factor_units_reachable']
assert not records['conditional']['carrier65_reachable'] and not records['instantiated']['carrier65_reachable']
print(json.dumps({'status':'PASS','inputs':{str(k.relative_to(TASK)):v for k,v in PINS.items()},'exact_one_import_edit':True,'new_imports':newimports,
 'frontiers':records,'limits':['Source-only; no Lean execution, provider authentication or build-readiness claim.',
 'Reachability is relative to the pinned predecessor source graph, using static initial imports only.',
 'Object presence does not establish compatible objects, source provenance or complete package closure.',
 'The 87 parent PolynomialBridge is still an explicit assumption in the conditional endpoint.']},sort_keys=True,indent=2))
