import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-named-formula-draft'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'FORMULA.md':'2ae78c33cf6f5f9a6096918aee8475c72adc205abbd6a954c69e7e06b457081c','Norm38NamedFormula.lean':'a5a8db6833252881c37016f3b28e006168db45a8119074b04572c8341d2593e6','check_sources.py':'48aa58cf8def8dfc18daf99c55a79042b065acff0b30a5ed96f83cb69db5cc97','source-survey-result.json':'83ae35b6fc8e582d9d51fc3c80f6e42c2a5ce552d13e74ab9d2580ae02af1ed5'}
for n,h in pins.items():assert sha(p/n)==h
x=subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check_sources.py')],timeout=60);assert hashlib.sha256(x).hexdigest()==pins['source-survey-result.json'];assert json.loads(x)['status']=='PASS_POINT_IN_TIME_SOURCE_OBJECT_SURVEY'
f=(p/'FORMULA.md').read_text();s=(p/'Norm38NamedFormula.lean').read_text()
for x in ['ν=38','L=5^39','Fin 40 → ℕ','k_{j+1} · 5^j','∏_{j=0}^{39} k_j!','2^(2 + Σ_{k∈Star} |p(k)|)','toNat(Σ_{k∈Star} (z + p(k)) · (2z)^(L - expo(k)))','ℓ = Σ_{j=0}^{37} B^(5^(j+1))','λ = Σ_{j=0}^{4L-1} B^j','G = 32b · B^(5^38)','K_c=B_d(2D_m-1)','(T² + K_c²A₀ - K_c²V₀²A₁)² - 4T²K_c²A₀']:assert x in f,x
for x in ['Norm38IPRAEndpoint.expression.evalRing a','let ν := 38','let seed := SharingSeed38.seed CurrentWindowCarry2011.ports','let z := indexZ seed 0','let y := indexY seed 0','let aa : Fin 10 → R := Fin.cons 1 a','RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (a 8) v.dvsr v.dvnd v.marg','ModelJonesSyntax.evalRing_expression','ModelJonesSyntax.mapVars_syntaxVars']:assert x in s,x
print(json.dumps({'status':'PASS_MANUAL_FORMULA_SOURCE_REVIEW','pins':pins,'scope':'Manual comparison of named formula to pinned Lean source; source survey is point-only; Lean client uncompiled and text is not Lean-read.'},indent=2,sort_keys=True))
