from pathlib import Path
import re,hashlib,json
D=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
n=(D/'NativeAdaptiveGraph.lean').read_text().split('  -- BEGIN INPUT ALIASES\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
a=(D/'AdaptiveEquationSyntax2011.lean').read_text().split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 13) :=\n',1)[1].split('\n  P13\n',1)[0]
n=n.replace('  -- END INPUT ALIASES\n','').replace('  -- BEGIN LITERAL GRAPH\n','').strip()
a=re.sub(r'let (\w+) : Expr \(Fin 13\) := \.var (\d+)',r'let \1 := x \2',a)
a=re.sub(r'let (\w+) : Expr \(Fin 13\) := \.constant \(p (\d+)\)',r'let \1 := ports \2',a).strip()
assert a==n,'gate sequence or aliases differ'
rows=[x for x in n.splitlines() if x.strip().startswith('let ')]
assert len(rows)==105, len(rows)
print(json.dumps({'status':'PASS','aliases':17,'gates':len(rows)-17,'source_sha256':hashlib.sha256((D/'NativeAdaptiveGraph.lean').read_bytes()).hexdigest(),'binding_sha256':hashlib.sha256((D/'AdaptiveEquationSyntax2011.lean').read_bytes()).hexdigest()},indent=2))
