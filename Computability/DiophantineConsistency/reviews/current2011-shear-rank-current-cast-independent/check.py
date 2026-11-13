#!/usr/bin/env python3
"""Review generic tsub and fixed 4-port model cast, without Lean."""
import hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-rank-cast-generic-draft/README.md':'70f0e96926c70276c244133cfc764780d003e4e5dc77605361c540a3860b4a93',
'research/current2011-shear-rank-cast-generic-draft/RankCast.lean.src':'e66627d9c499e178cfb5005aaad5188fd05ba8d6586d7627be28e654b5f2b602',
'research/current2011-shear-rank-cast-generic-draft/check.py':'d4831f27461b32df4f3f38afc54858110fbc52f082657e4edfbbda974ccd33f7',
'research/current2011-shear-rank-cast-generic-draft/result.json':'4824b86a55bc027a788dfc5549b66a9526bcf7e78981cf8bf20edbb0f297f917',
'research/current2011-shear-current-port-cast-draft/README.md':'2166cdf0315198b939d8491e3da3f05a99659df4783c60fef0c959d41fe5bfba',
'research/current2011-shear-current-port-cast-draft/CurrentPortCast.lean.src':'be27b59b37e99d41eb90f6913ef6f19f0d943581c51ded85477477e9f46fc320',
'research/current2011-shear-current-port-cast-draft/check.py':'15a36f1526890a50525a8c71635a945d3aa8cecc9b60a50c7b6e50700512dd3f',
'research/current2011-shear-current-port-cast-draft/result.json':'2bb9acf4f1566f859bf12f8dec6802c3c6afc52f44bf768d7df068ac9f5946ad',
'Lean/DiophantineConsistency/CurrentKernelData2011.lean':'529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c',
'Lean/DiophantineConsistency/CurrentMaskData2011.lean':'8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582',
'Lean/DiophantineConsistency/Carrier65.lean':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'Lean/DiophantineConsistency/ArithmeticCarrierRadix2011.lean':'87f89c10bd5499a4c7586d36138ded09fdcdb6968b16b954d30c1e335950c074',
'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a'}
def need(b,m):
 if not b:raise RuntimeError(m)
for path,h in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==h,'pin '+path)
def read(p):return (root/p).read_text()
s=read('research/current2011-shear-rank-cast-generic-draft/RankCast.lean.src');t=read('research/current2011-shear-current-port-cast-draft/CurrentPortCast.lean.src')
for x in ['(h : b ≤ a)', '(h1 : 1 ≤ q)', '(hF : F ≤ q)', '(h2 : 1 ≤ q^2)', 'theorem gap_implies_F_le_q','tsub_add_cancel_of_le h']:
 need(x in s,'generic '+x)
for x in ['import ForwardIndex','import RankCast','theorem currentP_eq_embedded (j : Fin 4)', '(CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ)', 'theorem core_q_cast','theorem core_c_cast','theorem core_rank_cast','theorem ring_half_at_parent_zero','core_rank_cast v hF','core_c_cast v']:
 need(x in t,'current '+x)
need('![beta, K, lowPort, highPort + beta]' in read('Lean/DiophantineConsistency/CurrentMaskData2011.lean'),'integer mask tuple')
need('CurrentMasks2011.ports (K : ℤ)' in read('Lean/DiophantineConsistency/CurrentKernelData2011.lean'),'current tuple')
core=read('Lean/DiophantineConsistency/Carrier65.lean');need('let b := p 0 * J' in core and 'let rank := (b * (q - F) + alpha)' in core,'signed rank source')
# Independent small concrete current tuples; rank covers all three tsub cuts.
count=0
for beta in range(1,5):
 for K in range(3):
  for low in range(3):
   for high in range(3):
    ports=[beta,K,low,high+beta];need(ports[3]==high+beta,'high shift')
    for J in range(1,5):
     q=beta*J+1
     for F in range(q+1):
      for alpha in range(3):
       sub=lambda a,b:max(a-b,0)
       natural=((sub(q,1)*sub(q,F)+alpha)*sub(q*q,1)+(ports[2]+q*ports[3])*J)
       signed=((beta*J*(q-F)+alpha)*(q*q-1)+(ports[2]+q*ports[3])*J)
       need(natural==signed,'rank');count+=1
need(max(2-3,0)!=2-3,'missing F≤q counterexample')
print(json.dumps({'source_pins_verified':len(pins),'generic_tsub_and_gap_hypotheses_checked':True,'four_port_once_shift_checked':True,'concrete_rank_integer_controls':count,'scope':'source and finite controls only; cast simplification and model providers unelaborated'},indent=2,sort_keys=True))
