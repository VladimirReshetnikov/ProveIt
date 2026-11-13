#!/usr/bin/env python3
"""External reference-to-gate binding; no Lean replay."""
import contextlib,hashlib,io,json,re,runpy,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];src=D/'research/nine-sharing-norm38-reference-draft/Norm38Reference.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(src)=='14103a5da6245030f2e189aa13869514daf4be668bcdd2f521e1ec132f8c8ff0'
with contextlib.redirect_stdout(io.StringIO()):prior=runpy.run_path(str(D/'reviews/nine-sharing-norm38-model-bridge-draft-independent/check.py'))
with contextlib.redirect_stdout(io.StringIO()):carrier=runpy.run_path(str(D/'reviews/nine-sharing-quartic65-59-independent/source_check.py'))
s=src.read_text();rows=re.findall(r'^  let a(\d+) : R := (.+)$',s,re.M);assert [int(x) for x,_ in rows]==list(range(81))
for i in range(14):assert rows[i][1]==f'x {i}'
for i in range(4):assert rows[14+i][1]==f'p {i}'
for i,n in enumerate([1,3,4],18):assert rows[i][1]==str(n)
done=set(range(21)); op={'add':'+','sub':'-','mul':'*'}
for target,left,right,tag in prior['gates']:
 assert left in done and right in done and target not in done
 assert rows[target][1]==f'a{left} {op[tag]} a{right}';done.add(target)
assert done==set(range(81))
for gate,field in [('N0','P'),('N1','Q'),('Na','U'),('Nt','W'),('scaled_Ns','Z'),('Delta','delta')]:assert carrier['v'][gate]==carrier['env'][field]
for k in ['NormAssignment38.gatesHold ι ports w','NormAssignment38.fiveNorms ι ports w','(hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))','Norm38SlotExtraction.seed_zero_static','FreshModel106.evalRing_expressionAt65','Fin.castLE (by decide : 14 ≤ 38)']:assert k in s
assert '(congrFun hfixed i).trans (hrun i hi)' in s
for i in (61,44,78,66,80,36):assert f'heq {i} (by decide)' in s
print(json.dumps({'status':'PASS_EXTERNAL_REFERENCE_BINDING_ONLY','source_sha256':sha(src),'nodes':81,'gates':60,'scope':'Source/graph and conditional implication review only; no Lean replay or zero bridge'},indent=2,sort_keys=True))
