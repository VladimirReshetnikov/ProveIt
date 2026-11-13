from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-bounded-formula-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-bounded-formula-draft/PellPeriodBounded.lean.src').read_text()
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
bnd=Path('Lean/DiophantineConsistency/StrictSigmaOneInduction.lean').read_text()
mapS=Path('Lean/DiophantineConsistency/ParsonsHierarchyMap.lean').read_text()
formula=Path('Lean/DiophantineConsistency/PRABoundedFormula.lean').read_text()
witness=Path('Lean/DiophantineConsistency/PRABoundedWitness.lean').read_text()
period=Path('research/ordinary13-explicit-pell-period-model-draft/ExplicitPellPeriod.lean.src').read_text()
# Inspect quote and exact variable order without assuming Lean has elaborated it.
match=re.search(r'def periodDef : 𝚺₁\.Semisentence 2 := \.mkSigma\s*“(.*?)”',P,re.S);assert match
compact=lambda x:re.sub(r'\s+','',x)
assert compact(match.group(1))==compact('m a. ∃ c h x y r t, !yDef c m a ∧ h=2*m*c ∧ !xDef x h a ∧ !yDef y h a ∧ x=1+c*c*r ∧ y=t*c*c')
for name,projection in [('xDef','π₁'),('yDef','π₂')]:
 s=re.search(r'def '+name+r' : 𝚺₁\.Semisentence 3 := \.mkSigma\s*“(.*?)”',rec,re.S).group(1)
 assert compact(s)==compact('out time b. ∃ state, !runDef state time b ∧ !'+('pi₁Def' if name=='xDef' else 'pi₂Def')+' out state')
assert 'instance x_defined : 𝚺₁-Function₂[V] xcoord via xDef' in rec
assert 'instance y_defined : 𝚺₁-Function₂[V] ycoord via yDef' in rec
assert 'def boundedPeriod : ArithmeticSemisentence 3 := bnd periodDef.val' in P
for x in ['abbrev lastVar (n : ℕ) : ArithmeticSemiterm ξ (n + 2) := #(Fin.last (n + 1))',
 'def bnd : {n : ℕ} → ArithmeticSemiformula ξ n → ArithmeticSemiformula ξ (n + 1)',
 '| n, ∃⁰ φ => ∃⁰[“x. x < !!(lastVar (ξ := ξ) n)”] bnd φ',
 '(f : ξ → M), (bnd φ).Eval (Fin.snoc e w) f → φ.Eval e f']:
 assert x in bnd,x
assert '(h : Hierarchy Γ s φ) : s ≤ 1 → (s = 1 → Γ = 𝚺) → Hierarchy 𝚺 0 (bnd φ)' in bnd
assert 'exact hierarchy_bnd periodDef.sigma_prop (by decide) (by intro _; rfl)' in P
assert 'Hierarchy Γ s (Semiformula.lMap embedding φ)' in mapS
assert 'exact ParsonsHierarchyMap.hierarchy boundedPeriod_hierarchy' in P
assert '(h : Hierarchy 𝚺 0 φ)' in formula and '∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧ PRA ⊢ oneCorrectSentence c φ' in formula
assert '∃ code : Code 3, Primrec (eval code) ∧ PRA ⊢ bitSentence code' in P
assert 'PRA_proves_boundedBooleanCharacteristic _ mapped_boundedPeriod_hierarchy' in P
assert 'theorem characteristicMatrix_open' in witness and 'characteristicMatrix_open code' in P
bridge=re.search(r'def PeriodEvaluationBridge : Prop :=(.*?)\n\n/--',P,re.S).group(1)
for x in ['periodDef.val.Evalb ![m,a] ↔','c=ycoord m a','h=2*m*c','x=xcoord h a','y=ycoord h a','x=1+c*c*r','y=t*c*c']:assert x in bridge
assert 'theorem period_holds_if_evaluation (bridge : PeriodEvaluationBridge)' in P
assert 'apply (bridge V m a).mpr' in P and 'period_at_twice_index_ordinate m a' in P
assert 'theorem period_at_twice_index_ordinate (m a : V)' in period
# Independent fast recurrence and modest growth checks; not a bound theorem.
def matmul(a,b):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i in range(2) for j in range(2))
def power(n):
 x=(1,0,0,1);q=(2,3,1,2)
 while n:
  if n&1:x=matmul(x,q)
  n//=2
  if n:q=matmul(q,q)
 return x
for m in range(1,5):
 c=power(m)[2];h=2*m*c;y=power(h)[2]
 assert c>=2**(m-1) and y>=h>=m*2**m
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'quoted_variable_scopes_and_Pell_graph_arguments_inspected':True,
 'last_bound_and_strict_less_source_inspected':True,'hierarchy_and_characteristic_interfaces_inspected':True,
 'evaluation_bridge_remains_unproved':True,'growth_controls':4,
 'lean_elaboration_or_provider_checked':False,'ipra_existence_proved':False,'lean_executed':False},indent=2,sort_keys=True))
