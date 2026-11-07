#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed38-jones-vars-bd-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'83fe59cc59138c306b1c570821e1b860b9df17874426b531e6b120bc8ddaf4b0','provider_preflight.py':'9c9d4c0abe95e56791be83f64e08a2a054de13599c31cb0c405afece3df7bbbd','source-manifest.json':'6af03c711018c48ec7d1bff59e59e313cd458b530a39e035d20278468fa39a0e','src/DiophantineConsistency/Norm38MacroVarsBd.lean':'3b3e3dbfef6652d6de7b20fdf55007e9d7976f1bfc287e593b21aecd252d590c'}.items():assert sha(P/n)==h
r=json.loads((P/'source-manifest.json').read_text())['rows'];assert len(r)==1 and r[0]['imports']==['DiophantineConsistency.Norm38MacroTerminalOutput']
p=P/'src/DiophantineConsistency/Norm38MacroVarsBd.lean';s=p.read_text();assert re.findall(r'^theorem (\w+)',s,re.M)==['d41_Bd_eq_dvsr']==re.findall(r'^#print axioms (\w+)',s,re.M)
fields=s.split('def vars ',1)[1].split(':=',1)[1].split('\n\ntheorem',1)[0];fields=''.join(fields.split());want='⟨d11.valuesa(Fin.last10),((basea^(5:Nat))^(5^39:Nat))^(16:Nat),basea,a⟨1,bydecide⟩+((1:Int):R),((32:Int):R)*basea*(basea^(5:Nat))^(5^38:Nat),a⟨2,bydecide⟩+((1:Int):R),a⟨3,bydecide⟩+((1:Int):R),a⟨4,bydecide⟩+((1:Int):R),a⟨5,bydecide⟩,a⟨6,bydecide⟩+((1:Int):R),a⟨7,bydecide⟩+((1:Int):R)⟩';assert fields==want
core=(D/'Lean/DiophantineConsistency/JonesSyntaxCore.lean').read_text();assert '(R N b g G h s w φ i j : A)' in core and 'def dvsr : R := (v.J * v.F) ^ 2' in core
named=(D/'research/nine-seed38-jones-named-formula-check/src/DiophantineConsistency/Norm38NamedFormula.lean').read_text();assert 'let aa : Fin 10 → R := Fin.cons 1 a' in named and 'let v : RingVars R := ⟨rankCode (aa 0) (z : R) b e g l n q θ lam, n, b, g,' in named and '32 * b * B ^ (5 ^ ν), aa 3 + 1, aa 4 + 1, aa 5 + 1, aa 6, aa 7 + 1, aa 8 + 1⟩' in named
assert 'd41.values a ⟨39, by decide⟩ = (vars a).dvsr' in s and 'lookup40_41 a (Fin.last 39)' in s and 'rw [hb, d40_Bd_value]' in s
pre=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not pre.stderr;x=json.loads(pre.stdout);assert x['status']=='PASS_NO_LEAN_PREFLIGHT' and x['stage_count']==1
print(json.dumps({'status':'PASS_NO_LEAN','preflight':x,'scope':'Bd cut = vars.dvsr with d11 rank opaque; correspondence of vars to named formula remains separate'},indent=2,sort_keys=True))
