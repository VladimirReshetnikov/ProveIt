#!/usr/bin/env python3
"""Fresh isolated unit test of the inspected adapter's exact facade class.
No science/audit packet source is executed or altered. This extracts only the
adapter class AST, preserving that class, and supplies disposable path roots.
"""
from pathlib import Path
import ast,hashlib,json,os
BASE=Path('/workspace/shared/review-replay-projective62-20261004')
ADAPTER=Path('/workspace/shared/replay-projective-signal-shears62-20261004/replay.py')
source=ADAPTER.read_bytes();tree=ast.parse(source)
function=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='execute_owned_checker')
facade=next(n for n in function.body if isinstance(n,ast.ClassDef) and n.name=='RoutedPath')
root=BASE/'facade_collision_fixture';root.mkdir(exist_ok=False)
science=root/'science';audit=root/'historical_science';output=root/'output'
for p in [science,audit,output]:p.mkdir()
evidence=output/'evidence';evidence.mkdir()
checker=audit/'independent_static_audit.py';checker.write_text('# Inert path fixture only; not executable audit code.\n')
def need(condition,message):
    if not condition:raise RuntimeError(message)
env={'os':os,'Path':Path,'science':science,'audit':audit,'output':output,'evidence':evidence,'allowed_reads':{science,audit,output},'HISTORICAL_SCIENCE':str(audit),'need':need}
exec(compile(ast.Module(body=[facade],type_ignores=[]),str(ADAPTER),'exec',dont_inherit=True,optimize=0),env)
RoutedPath=env['RoutedPath'];checks={}
checks['direct_historical_constructor_maps_to_science']=RoutedPath(str(audit)).p==science
actual=RoutedPath(str(checker))
checks['checker_self_path_remains_actual']=actual.p==checker
checks['derived_resolved_parent_stays_actual_audit']=actual.resolve().parent.p==audit
checks['derived_parent_evidence_routes_to_fresh_output']=(actual.resolve().parent/'evidence').p==evidence
checks['derived_audit_resolve_stays_audit']=actual.parent.resolve().p==audit
checks['glob_returns_actual_audit_checker']=[p.p for p in actual.parent.rglob('*.py')]==[checker]
result={'passed':all(checks.values()),'adapter_sha256':hashlib.sha256(source).hexdigest(),'checks':checks,'packet_code_executed':False,'method':'Exact adapter class AST extracted into a disposable-root unit test; original input trees untouched'}
(BASE/'facade_edge_result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));raise SystemExit(0 if result['passed'] else 1)
