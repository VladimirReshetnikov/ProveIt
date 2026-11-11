#!/usr/bin/env python3
"""Literal graph and model-route source audit; no Lean or build."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-guarded-fold89-lean-draft'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','78be85d8dfcbddd715e3eba3d6c915e5cae81eb9d2beab0f8f64527ac12b6b1e'),(P/'make_graph.py','2f06e915c2500927ec6bfa63998ca9edad39017993a739dfae04a73dba28dc19'),(P/'P89GuardedGraph.lean','dec582dd7baba5a10bee20fd6673720c81a00d85334b026b251e9a4fcc319c2a'),(P/'observation.json','61771431dce6897ea2341a559975ed79a59cbdeb2559d03388c9d41573cee5ce')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent source review is recorded in\n`../../reviews/ordinary14-guarded-fold89-lean-draft-independent/`.\n';assert readme.endswith(tail); prior=readme[:-len(tail)];assert prior.count(b'the available `exp_add`')==1;prior=prior.replace(b'the available `exp_add`',b'the existing the available `exp_add`');assert hashlib.sha256(prior).hexdigest()=='5fb83107bcb75f6b9c14c8c3d4b6b3e615c6cea8f4a84a5caa0b92992388b92d'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'make_graph.py'),'--check'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=30);assert not r.stderr and r.stdout==(P/'observation.json').read_bytes()
gp=D/'research/ordinary14-guarded-fold89-26/candidate.json';assert sha(gp)=='4f0758dd44c61c72c7ac19b244336306bcb588f600debe6b4dbdb686916a6012';g=json.loads(gp.read_text());s=(P/'P89GuardedGraph.lean').read_text();block=s.split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0];rows=[]
for line in block.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert m,line
 n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
assert rows==g['source'] and len(rows)==89
for i,n in enumerate(g['witnesses']):assert f'let {n} : Expr (Fin 14) := .var {i}' in s
for i,n in enumerate(g['fixed_numerals']):assert f'let {n} : Expr (Fin 14) := .constant (p {i})' in s
assert '⟨A0, A1, Fa, g72, Bt, guarded_out⟩' in s and '(graph p).Bt - .var 13' in s and 'by rfl' in s
base=D/'Lean/DiophantineConsistency';sources={'ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884','ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5','Compact44/CompactSeedOrdinate.lean':'d7141305340a682947e88f68fa65305aa3de643c3f31790ce6a846a7bacd0af5','Compact44/CompactFirstPositive.lean':'dce31c66f5336a822ad9c27dbb5a2d1af25bf977c223cd366399d5345e7e2c8f','Compact44/CompactFixedBeta.lean':'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea','Compact44/CompactCellProductBound.lean':'bdf642a54f609caf3a09d08ea529079fbc201414ac390566fd5c10a88a9a2c22','Compact44/FreeJ13Halt.lean':'18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a','Compact44/FreeJFirstTransport.lean':'3d806de318b1c798e8b2a31ca14e790a14d09b3996acf9c4c3346d3fc42c2029','Compact44/FreeJRootBinding.lean':'7e395c9461414fef818fe1319aad1a31bbd62536ea143c66c8e8134c1ed00b01','Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091'}
t={}
for n,h in sources.items():assert sha(base/n)==h;t[n]=(base/n).read_text()
for n,ss in {'ArithmeticAdaptiveQuotients2011.lean':['theorem scaled_quotient','dvd_of_square_dvd','z*z=m*m*n'],'ArithmeticPellFirstNorm.lean':['theorem positive_parameter_solution','theorem descent'], 'Compact44/CompactSeedOrdinate.lean':['theorem seed_ordinate_le_k','(ht : 2≤time)'], 'Compact44/CompactFirstPositive.lean':['theorem positive_first_carrier','(hq : 2≤q-1)','(hs : sY≤k)'], 'Compact44/CompactFixedBeta.lean':['theorem beta_identity','theorem bounds'], 'Compact44/CompactCellProductBound.lean':['theorem symbolic_kernel_lt','592884'], 'Compact44/FreeJ13Halt.lean':['theorem forward','∃ x : Fin 12'], 'Compact44/FreeJFirstTransport.lean':['theorem freej_first_factor_transport','(hv : ∀j,0<v j)'], 'Compact44/FreeJRootBinding.lean':['theorem first_root_quotient','theorem folded_quotient_forces_Y_divisible'], 'Compact44/P72Root.lean':['theorem ι_magnitude_sq']}.items():
 for token in ss:assert token in t[n],(n,token)
assert 592884<2*(67*8807)
print(json.dumps({'status':'PASS_SOURCE_ONLY','literal_rows':len(rows),'source_routes_checked':len(sources),'generator_observation_reproduced':True,'scope':'uncompiled source proposal; graph-specific model clients, provider closure and arbitrary-model proof remain open; no Lean'},indent=2))
