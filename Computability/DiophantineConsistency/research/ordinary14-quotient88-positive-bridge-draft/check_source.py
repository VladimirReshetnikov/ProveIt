from pathlib import Path
import hashlib,json,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'Quotient88PositiveBridge.lean').read_text()
for t in ('Parent88EquivalenceDraft.positive_zero_iff','P88FourSquareModel.positiveBridge','CompactSymbolicModelIff.p','paramKernel rho','C44Short15Facts.port_bounds','hpair.symm.trans'):assert t in s
for name in ('ordinary13-14-parent-88-model-equivalence-draft','ordinary13-freej88-four-square-lean-draft'):
 r=D/'research'/name;f='check_source.py' if (r/'check_source.py').exists() else 'make_graph.py'
 if f=='make_graph.py': continue
 x=subprocess.run([sys.executable,'-I','-S','-B',str(r/f)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
print(json.dumps({'scope':'symbolic positive bridge source composition, no Lean','lean_run':False,'source_sha256':hashlib.sha256((p/'Quotient88PositiveBridge.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
