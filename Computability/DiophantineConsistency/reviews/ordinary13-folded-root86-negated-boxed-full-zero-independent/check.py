#!/usr/bin/env python3
"""Independent boxed-port scalar and inherited witness audit; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-negated-boxed-full-zero';toy=D/'reviews/ordinary13-folded-root86-toy-full-zero-independent';floor=D/'reviews/current14-carrier64-pell-floor-independent';forward=D/'reviews/ordinary13-folded-root86-negated-forward-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','0ccb47e34a8ff08d99a98c049f9d086988235c5b714d819f4f9585ffb01e667c'),(P/'check.py','250e42cf7d0065f59e4414704799c5cef7e830da8ea9909c860959af4b82d8ce'),(P/'result.json','87d29e4e27aa29ac2e866b219d7fabdd2b26cfc629ded171d82e23440911fc7f'),(toy/'check.py','19b05a2069655a6eacfa91d0824afad080fe83201ba358da3e710c66b431752b'),(toy/'result.json','900aebfa8b65363d44e889525fc0eeb6c0b6b6c356fdec94f99db8f43260bf3a'),(floor/'check.py','65ff9800b15d3313eaecb3f595851f355f9e7b0c8f811afd46187cc95c9f6839'),(floor/'result.json','042e585bfc7e47b8212eabeb5271cdb8b2e5e9b64f28e53e995f2690fbe9b0b3'),(forward/'check.py','a17d6254b2498e2ea3ff6973f290eafb8387d1079d5704a51c063772eb587c83'),(forward/'result.json','f389d54e714a5d51272fcbcb883a7fc27d9bfb7381b380bca313312c177f668e')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-boxed-full-zero-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='30b18416d9a6e4568b1f8e9aa207f392c0472a623f54245792f94984def6fbb4'
for p in (P,toy,floor,forward):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
b,q=31,32;J,F,alpha=1,1,45;beta,K,MC,MF=31,9,13,55
G=b*(q-F)+alpha;R=G*(q*q-1)+J*(MC+q*MF);N=(R-1)//2
assert 0<MC<beta<MF<2*beta and (G,R)==(1006,1030911) and R%4==3 and R>=26
assert N.bit_count()-1==15 and pow(2,R,b)==2 and ((q-F-alpha)*(pow(2,R,b)+K*q)-F*q)%b==0
assert q*(q-1)-G==-14 and q-F-alpha==-14
# R fixes G because q²−1>0; then C=q(q−F)−G≤−14 for every F≥1.
for ff in range(1,1000):assert q*(q-ff)-G<=-14
g=json.loads((D/'research/ordinary13-folded-root86-negated/candidate.json').read_text());rows={r[0]:r for r in g['source']}
for n,row in {'C':['C','-','qF','alpha'],'G':['G','+','alpha','g44'],'Bt':['Bt','-','g27','g28'],'R':['R','+','g47','g50'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items():assert rows[n]==row
print(json.dumps({'status':'PASS_SCOPED_BOXED_TOY','ports':[beta,K,MC,MF],'G':G,'R':R,'Y_two_adic_valuation':15,'X_mod_31':pow(2,R,b),'scope':'symbolic boxed toy zero and fixed-rank obstruction; no actual-port or unrestricted nonequivalence claim; no Lean'},indent=2))
