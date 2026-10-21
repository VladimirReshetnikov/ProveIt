#!/usr/bin/env python3
"""Replay an unchanged symbolic engine against an exact new 218-state table.

These are mathematical induction checks over arbitrary natural register values
and finite spare lists, not a proof-assistant kernel certificate. Calibration
of the source calculus and blank startup are separate obligations.
"""
import argparse, hashlib, json, sys, time
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor'
DEPENDENCIES = {
 'portable/build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
 'portable/source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
 'portable/runtime/vendor/symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
 'portable/runtime/vendor/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
 'portable/runtime/reference_results/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf',
}
VARIANTS = {
 'omit-zero':{
  'table':'7d820254e777eb96108887f5ef6d6c2ae8af8ce70b8728dcdcdc97f85ec235d8',
  'source':'86ca1b05c5bfada9d77ece84b88a165a7d61fe3dd8623273d94d1e81f87ac8e3',
  'cases':6142,'rules':1511359,'leaves':4725},
 'dmn':{
  'table':'0e2b4c9fb78158c69b95bf854d34ac256f63acffd6224b5108806ace638f46f1',
  'source':'0853a3237ee5c09a1866f649006993e00cab1622c51aaaaf31844700df49e613',
  'cases':6167,'rules':1516795,'leaves':4744},
}
def require(ok, message):
 if not ok: raise ValueError(message)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p, value): p.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('variant',choices=VARIANTS)
 ap.add_argument('--output',type=Path)
 a=ap.parse_args()
 require(__debug__ and not sys.flags.optimize,'Python assertions must be enabled')
 for name,h in DEPENDENCIES.items(): require(digest(VENDOR/name)==h,'Dependency: '+name)
 sys.path[:0]=[str(VENDOR/'portable'),str(VENDOR/'portable/runtime/vendor')]
 import build221 as builder
 import source_language as source
 import symbolic_runtime as runtime
 cfg=VARIANTS[a.variant];d=ROOT/'variants'/a.variant
 table_path=d/'machine.native.tm';source_path=d/'source.sites.json'
 require(digest(table_path)==cfg['table'],'Table identity')
 require(digest(source_path)==cfg['source'],'Source identity')
 table=builder.read_table(table_path.read_bytes());sites=json.loads(source_path.read_text())
 tree=source.tree(sites);metrics=source.metrics(tree)
 require(source.sites(tree)==sites,'Source ordinal order')
 require(source.graph_arithmetic(sites)[0]==source.graph_intervals(sites),'Two source CFGs')
 require(metrics==dict(dag_nodes=205,leaf_occurrences=cfg['leaves'],maximum_depth=38,maximum_zero_run=6),'Source metrics')
 working={q for q,b in table}
 require(len(working)==218 and len(table)==436,'Working-state census')
 mapping={int(q):int(z)for q,z in json.loads((VENDOR/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
 for q in working|{254}:mapping.setdefault(q,q+1000)
 require(len(set(mapping.values()))==len(mapping),'Injective legacy mapping')
 legacy={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in table.items()}
 out=a.output or ROOT/'reproduced'/('runtime-'+a.variant)
 out.mkdir(parents=True,exist_ok=True)
 started=time.monotonic();lemmas,blocks=runtime.prove_blocks(legacy)
 cases=[];used=set()
 for i,s in enumerate(sites):
  for positive in ((False,True)if s[1]=='CD'else(False,)):
   answer=runtime.case(legacy,lemmas,s,positive)
   used.update(answer.pop('rows'));answer.pop('trace')
   cases.append({'index':i,'positive':positive,**answer})
  if len(cases)%1000==0:print(a.variant,'proved',len(cases),flush=True)
 require(len(cases)==cfg['cases'],'Full guard census')
 require(sum(x['symbolic_steps']for x in cases)==cfg['rules'],'Exact symbolic rule census')
 inverse={v:k for k,v in mapping.items()};native_rows=sorted((inverse[q],b)for q,b in used)
 require(native_rows==sorted(table),'All rows used')
 require(min(x['duration'][0]for x in cases)==12,'Positive durations')
 receipt={
  'status':'ALL_PRIMITIVE_INTERFACES_PROVED','variant':a.variant,
  'working_states':218,'transition_rows':436,'source_metrics':metrics,
  'cases':len(cases),'expected_cases':cfg['cases'],'symbolic_steps':cfg['rules'],
  'minimum_actual_steps':12,'table_sha256':cfg['table'],'sites_sha256':cfg['source'],
  'driver_sha256':digest(Path(__file__)),'dependencies':DEPENDENCIES,
  'block_schemas':blocks,'directly_used_native_rows':native_rows,
  'debug_enabled':True,'python_version':sys.version,'seconds':time.monotonic()-started,
  'proof_scope':'All source leaves and both decrement guards; independent arbitrary natural register values, natural extra gap, arbitrary first spare value, arbitrary finite remaining spare list; complete endpoint tape and strictly positive duration. Mathematical induction, not proof-assistant kernel checking.',
  'bounds_scope':'4000 bounds symbolic proof construction only, not natural values or actual runtime.',
  'external_obligations':['Modified source semantics and proof-enumerator calibration','Exact blank startup']}
 dump(out/'runtime.json',receipt);dump(out/'cases.json',cases)
 print(json.dumps({k:receipt[k]for k in ['status','variant','cases','symbolic_steps','minimum_actual_steps','seconds']},indent=2),flush=True)
if __name__=='__main__':main()
