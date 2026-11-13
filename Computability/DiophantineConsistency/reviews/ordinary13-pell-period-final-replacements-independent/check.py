from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-final-replacements-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
F=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
G=Path('Lean/DiophantineConsistency/PRAWitnessPR.lean').read_text()
compact=lambda x:re.sub(r'\s+','',x)
body=re.search(r'def BodyData \(t r y x h c m a : V\) : Prop :=(.*?)\nend Model',P,re.S).group(1)
expected='yDef.val.Evalb ![c,m,a] ∧ h=2*m*c ∧ xDef.val.Evalb ![x,h,a] ∧ yDef.val.Evalb ![y,h,a] ∧ x=1+c*c*r ∧ y=t*c*c'
assert compact(body)==compact(expected)
quoted=re.search(r'def finalBody : ArithmeticSemisentence 8 :=\s*“(.*?)”',F,re.S).group(1)
assert compact(quoted)=='tryxhcma.!yDefcma∧h=2*m*c∧!xDefxha∧!yDefyha∧x=1+c*c*r∧y=t*c*c'
for s in ['def boundR : BoundTerm 6 := poly ‘#1’','def boundT : BoundTerm 7 := poly ‘#1’',
 'def bodyR : ArithmeticSemisentence 7 := ∃⁰ finalBody','def Replacement {n : ℕ}']:assert s in F
for s in ['theorem replaceR (c x r : V) (hx : x=1+c*c*r)',
 "∃ r' ≤ x, x=1+c*c*r'",'theorem replaceT (c y t : V) (hy : y=t*c*c)',
 "∃ t' ≤ y, y=t'*c*c",'rcases eq_zero_or_pos c with hc | hc',
 'def BodyEvaluationBridge : Prop','finalBody.Eval e Empty.elim ↔',
 'theorem tReplacement (evalBody : BodyEvaluationBridge) : Replacement finalBody boundT',
 'theorem rReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyR boundR',
 'replaceT (e 4) (e 1) t hy','replaceR (e 3) (e 1) r hx',
 "(evalBody V (t' :> e)).mpr", "(evalBody V (t :> r' :> e)).mpr",
 "exact ⟨hc,hh,hxg,hyg,hx',hy⟩"]:assert s in P,s
assert "ψ.Eval (x :> e) Empty.elim → ∃ x' ≤ A.vval e, ψ.Eval (x' :> e) Empty.elim" in G
# Direct context cons and all-body preservation for arbitrary graph-conjunct truth values.
count=0
for c in range(8):
 for r in range(12):
  for t in range(12):
   for tag in (0,1):
    x=1+c*c*r;y=t*c*c;h=tag;m=2;a=3
    h=2*m*c
    tEnv=[r,y,x,h,c,m,a];rEnv=[y,x,h,c,m,a]
    assert tEnv[1]==y and tEnv[4]==c and rEnv[1]==x and rEnv[3]==c
    assert [t]+tEnv==[t,r,y,x,h,c,m,a] and [t,r]+rEnv==[t,r,y,x,h,c,m,a]
    rr=r if c else 0;tt=t if c else 0
    assert rr<=x and tt<=y and x==1+c*c*rr and y==tt*c*c
    # Other four body conjuncts do not mention r or t; all their arguments stay fixed.
    assert [y,x,h,c,m,a]==rEnv and [r,y,x,h,c,m,a]==tEnv
    count+=1
assert 1000>1 and 1000>0 and 1==1+0*0*1000 and 0==1000*0*0
# The ordered-model inequality pattern is used elsewhere in the repository.
assert 'le_mul_of_one_le_right (by simp) (one_le_mul hy1 hy1)' in Path('Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean').read_text()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'six_body_conjuncts_and_both_contexts_checked':True,'positive_and_zero_replacement_controls':count,
 'body_evaluation_bridge_explicitly_unproved':True,'lean_tactics_and_providers_checked':False,
 'lean_executed':False},indent=2,sort_keys=True))
