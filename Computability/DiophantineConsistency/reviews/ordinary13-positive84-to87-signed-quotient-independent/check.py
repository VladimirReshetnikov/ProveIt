from pathlib import Path
from hashlib import sha256
from math import gcd
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale84To87.lean.src': '0ee0d013440902af45c4053a041eeb9596cb824cc1a2d13d5b3ff9d096ce4825', 'research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale87Graph.lean.src': 'cfb968caa89363a159fd24093d57eca5c80a86839a0798430a7b01fd557f2de8', 'research/ordinary13-positive84-to87-unscale-model-draft/README.md': '199a18359bc2608f7eaf5359752e55f0cee0aa08246578f18e18d54dfa3f51c2', 'research/ordinary13-positive84-to87-unscale-model-draft/receipt.json': 'beb0189ed2a761ec913999b977ff579cbe407c1695fd98fccd784e41b3806280', 'research/ordinary13-qcube93-model-draft/Ordinary13QCube93Arithmetic.lean.src': 'e9f61ed8c5e3262d9a316ef13cd15fa03dfc70a653c6ba7b85059aa9293be36d', 'Lean/DiophantineConsistency/ModelRelationCombining.lean': '559df80321efb3854759ca9dcb20277533bba2568863ddf8e5059d81ac0cc5d6', 'Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean': '4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885', 'research/ordinary13-aux-root87-36/candidate.json': 'abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
source,graph,readme,_,arith,square,reflect,gbytes=(Path(p).read_text() for p in PINS)
for token in ['def ScaledFirstCut','z=ι (cubeScale b)*ι b*t+ι (v 7)*ι b-ι (cubeScale b)*bt','z^2=(ι (cubeScale b)*ι b)^2*ι n','def ForwardNormBinding','(p 0 : DiffRing V)=ι beta ∧ ScaledFirstCut p v beta n','positive_quotient_of_signed_norm (v 0*beta) (v 7) n hy _ t _ hz hn','theorem forward_of_norm_binding','def ReverseRootCut']:
 assert token in source,token
for token in ['def cubeScale','theorem cube_bezout','theorem cube_dvd_of_dvd_mul','theorem positive_quotient_of_signed_norm','ModelRelationCombining.sq_dvd_sq','Trace75IntegralTransport.natural_dvd_of_signed']:
 assert token in arith,token
assert 'theorem sq_dvd_sq (m s : DiffRing V) (hm : m ≠ 0) (h : m ^ 2 ∣ s ^ 2) : m ∣ s' in square
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in reflect
g=json.loads(gbytes);r={row[0]:row for row in g['source']}
for row in [['q','+',1,'qm'],['q3','*','q','q2'],['M','*','q3','qm'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g39','*','M','M'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42']]:assert r[row[0]]==row
for b in range(20):
 h=(1+b)**3;assert h-b*(b*b+3*b+3)==1 and gcd(h,b)==1
valid=0;invalid_root_only=0
for b in range(8):
 h=(1+b)**3
 for y in range(1,55):
  for t in range(-2,3):
   for bt in range(-2,3):
    z=h*b*t+y*b-h*bt
    if b==0:
     if z==0:assert y%h==0;valid+=1
    elif z%(h*b)==0:
     assert y%h==0;valid+=1
    elif y%h!=0:invalid_root_only+=1
assert min(valid,invalid_root_only)>0
print(json.dumps({'sha256':PINS,'scaled_first_root_graph_rows_and_interfaces_checked':True,'bezout_values':20,'integer_divisibility_controls':valid,'root_without_norm_countercontrols':invalid_root_only,'lean_executed':False,'status':'Source-level quotient review and bounded integer controls; no model, import-provider, graph-cut or Lean validation.'},sort_keys=True,indent=2))
