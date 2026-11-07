#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-generic-polynomial-bridge-transport-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'0bee6f49beb8265319ff928ead7e411bd46020606f90d3d940ae4bacde70aa02','source-manifest.json':'d43f46d3895479e6630940450cd37201ffd38bd7cb353832f9a06b9323d76446','provider-survey.py':'6fa854001c4c55a5096fb7b373d3c1014a5c3a4a8f2b851de94ed63fb29226ef','src/DiophantineConsistency/GenericPolynomialBridgeTransport.lean':'b0dc3ab6322c0f3734f482ff7dcbb5d89c1effdd9831cba505964978a01aba00'}.items():assert H(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(m)==1 and m[0]['imports']==['DiophantineConsistency.HAExpressionAssembly','DiophantineConsistency.AdaptiveEquationSyntax2011'];s=(P/'src/DiophantineConsistency/GenericPolynomialBridgeTransport.lean').read_text()
for x in ['{m n : ℕ} (e : Expr (Fin m)) (f : Expr (Fin n))','(h : ∀ (V : Type) [ORingStructure V]','∃ w : Fin m → V, InternalZero e w','∃ w : Fin n → V, InternalZero f w','(hb : HAExpressionAssembly.PolynomialBridge f) : HAExpressionAssembly.PolynomialBridge e','not_congr (h V)']:assert x in s
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);assert not r.stderr and json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'generic bridge transfer requires both all-model zero iff and second bridge'},sort_keys=True,indent=2))
