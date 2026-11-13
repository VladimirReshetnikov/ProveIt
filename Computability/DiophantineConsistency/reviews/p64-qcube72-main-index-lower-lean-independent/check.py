#!/usr/bin/env python3
"""Read-only direct-guard audit of the checked IΣ₁-model index bound."""
import hashlib,json,os,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-main-index-lower-plan';O=P/'observations/attempt02'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
r=json.loads((O/'result.json').read_text());need(sha(O/'result.json')=='f7020ed3e27185738a23f4f0ab59bea41d993856645cd178dee83480ff91db6e','receipt pin')
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'terminal guards/status')
for path,entry in r['guards_before'].items():
 p=Path(path)
 if entry is None:need(not os.path.lexists(p),('unexpected',path))
 else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('changed guard',path))
need(r['object_sha256']=='27b2dac60724412a67574610fc5f613940fcf93bf403e1c61f3b5d2029cf18c1'==sha(r['command'][-1]),'object')
need(r['command'][-2]=='-o' and sha(r['command'][-3])==sha(P/'FreeMainIndexLower.lean')==sha(O/'FreeMainIndexLower.lean')=='4fe2970e9e05d818230d6fcf2eccb16b03567764b41e1a5f18f474c897559ab3','source')
need(sha(P/'check_lean02.py')==r['runner_sha256'] and sha(P/'missing_child.py')==r['missing_child_helper_sha256'],'runner')
need(sha(O/'compile.log')==r['log_sha256'],'log hash');text=(O/'compile.log').read_text()
need(not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text),'log error')
need(text.strip()=="'FreeMainIndexLower.six_le_index' depends on axioms: [propext, Classical.choice, Quot.sound]",'axiom report')
providers={'DiophantineConsistency/Compact44/P64Early':'9f9f46d3c82a74024d2e550df1074c3dc706c6242eb55235fa6bcc43d01341c2','DiophantineConsistency/ArithmeticPellPowerRecovery':'81ac9f2d4ffcf1ad8a5bce697cc6369a21a1df07aa9fdf10a8700e63755e392f','DiophantineConsistency/ArithmeticStandardCasts':'c992bafb003c67229c756a634d31c11ecfb942839904367554488ba27ddc597a'}
roots=r['lean_path'].split(':')
for mod,expected in providers.items():
 matches=[str(Path(root)/(mod+'.olean')) for root in roots if Path(root,mod+'.olean').is_file()];need(matches and matches[0] in r['guards_before'] and r['guards_before'][matches[0]]['sha256']==expected,('provider routing',mod))
s=(P/'FreeMainIndexLower.lean').read_text()
for x in ('[ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]','(q X Y U a H g c h m : V)','(hq : 33≤q) (hX : q≤X) (hY : 3≤Y)','(hU : U=Y*Y) (ha : a=X*Y+Y) (hH : H=4*a+3)','(hmx : xcoord m a=g) (hmy : ycoord m a=c)','(hcar : U*g=U*(X+a*c)+H*h) : 6≤m','projection_quotient a m','gcd_cancel H U (Exp.exp m) X','P64Early.gcd_dvd_nine X Y e heY heH','exp_monotone_le.mpr hm5'):
 need(x in s,('source fragment',x))
print(json.dumps({'status':'PASS','object_sha256':r['object_sha256'],'receipt_sha256':sha(O/'result.json'),'review_script_sha256':sha(__file__),'scope':'Recorded direct captured-provider, source, result and model theorem shape; no Lean or full transitive/dynamic provenance.'},sort_keys=True))
