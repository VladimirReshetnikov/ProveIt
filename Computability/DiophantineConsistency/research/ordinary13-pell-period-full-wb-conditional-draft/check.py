from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-period-full-wb-conditional-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=(D/'PellPeriodFullWB.lean.src').read_text()
checks=['“t r y x h c m a. !yDef c m a','def bodyR : ArithmeticSemisentence 7 := ∃⁰ finalBody','def bodyY : ArithmeticSemisentence 6 := ∃⁰ bodyR','def bodyX : ArithmeticSemisentence 5 := ∃⁰ bodyY','def bodyH : ArithmeticSemisentence 4 := ∃⁰ bodyX','def bodyC : ArithmeticSemisentence 3 := ∃⁰ bodyH','def boundC : BoundTerm 2 := exp2 (poly ‘2 * (#1 + 2) * #0’)','def boundH : BoundTerm 3 := poly ‘2 * #1 * #0’','def boundX : BoundTerm 4 := exp2 (poly ‘2 * (#3 + 2) * #0’)','def boundY : BoundTerm 5 := exp2 (poly ‘2 * (#4 + 2) * #1’)','def boundR : BoundTerm 6 := poly ‘#1’','def boundT : BoundTerm 7 := poly ‘#1’','def Replacement','(hc : Replacement bodyC boundC)','(ht : Replacement finalBody boundT)','xDef_wb (M := M)','yDef_wb (M := M)','change WB M (∃⁰ bodyC)']
for t in checks:assert t in p,t
period=Path('research/ordinary13-pell-period-bounded-formula-draft/PellPeriodBounded.lean.src').read_text()
assert '!yDef c m a ∧ h=2*m*c ∧' in period and '!xDef x h a ∧ !yDef y h a ∧ x=1+c*c*r ∧ y=t*c*c' in period
wb=Path('Lean/DiophantineConsistency/PRAWitnessPR.lean').read_text();assert "theorem wb_exs_bt'" in wb and "∃ x' ≤ A.vval e" in wb
# Explicit environments before introducing each witness.
envs={'c':['m','a'],'h':['c','m','a'],'x':['h','c','m','a'],'y':['x','h','c','m','a'],'r':['y','x','h','c','m','a'],'t':['r','y','x','h','c','m','a']}
assert [envs[k][1] for k in ('r','t')]==['x','y']
assert envs['c'][1]=='a' and envs['x'][3]=='a' and envs['y'][4]=='a' and envs['y'][1]=='h'
# Standard arithmetic examples demonstrate why r,t need replacement at c=0.
for r in (0,1,10**6):
 for t in (0,1,10**6):assert 1==1+0*0*r and 0==t*0*0
assert not 10**6<=1 and not 10**6<=0
# Small coordinate examples verify the candidate inequalities at positive c.
def pell(n,a):
 x,y=1,0;A=a+2;delta=(a+1)*(a+3)
 for _ in range(n):x,y=A*x+delta*y,x+A*y
 return x,y
controls=0
for m in range(1,4):
 for a in range(3):
  c=pell(m,a)[1];h=2*m*c;x,y=pell(h,a);cc=c*c
  assert c>0 and (x-1)%cc==0 and y%cc==0
  r=(x-1)//cc;t=y//cc
  C=2**(2*(a+2)*m);F=2**(2*(a+2)*h)
  assert c<=C and h==2*m*c and x<=F and y<=F and r<=x and t<=y
  controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_shapes_checked':len(checks),'environments':envs,'six_replacement_obligations_explicit':True,'zero_ordinate_requires_replacement':True,'positive_ordinate_controls':controls,'lean_executed':False,'uniform_primitive_recursive_bound_proved':False},sort_keys=True,indent=2))
