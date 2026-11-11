#!/usr/bin/env python3
"""Independent source-hypothesis and integer decoder audit; no Lean."""
import gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-shifted-guard87-calibration';Q=D/'reviews/ordinary14-shifted-guard87-probe-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','005fd2c04cef4c997383bf373cc48acd326e829eb01ff4d30c218dadaf9f758a'),(P/'check.py','142de39a368359171d5c37cb122fc22c91ac74450ac0523a1a2e46085fb346e7'),(P/'result.json','a8c6221eb05b6c86ec8db95d77d37cd77fc94a01c384ccf4ba411030318f8813'),(Q/'check.py','81e2e8d0374a0540519e022d4d87d9eff9ece51211a00cc4baae2e0685f7f731'),(Q/'result.json','cbd3b5c4d9677acd337063133ca0967a8f30df0419740ccdbe52f0d3fe62c55c')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-shifted-guard87-calibration-math-independent/`.\nA separate independent decoder review is recorded in\n`../../reviews/ordinary14-shifted-guard87-calibration-decoder-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='84f69c32b78b26a13056c3ef27041c4086c7d0ec444e9d1d9cd12770153a1eee'
for p in (P,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
base=D/'Lean/DiophantineConsistency';sources={'Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3','ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390','ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794','ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5','ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78','ArithmeticPellCongruences.lean':'75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1','Compact44/FreeJMainOrientation.lean':'d02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b','Compact44/FreeJEarlyIndex.lean':'ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d'}
t={}
for n,h in sources.items():assert sha(base/n)==h;t[n]=(base/n).read_text()
exact=t['Compact44/P72Exact.lean'].split('theorem indices_ordinary',1)[1].split(':= by',1)[0]
for token in ('(hq3 : 3 ≤ q)','(hX : 0 < X)','(hy0 : 0 < y0)','(hYq : Y = q * (q * q) * y0)','(hη : 0 < η)','(hc : c = η + Y * k)','(hi\' : 0 < i\')','(hf : 0 < f)','(ha : a = X * Y + Y)','(hR26 : 26 ≤ R)','(hny : 2 * ycoord n','(hks : k = 2 * n + 4 * ((X * Y) * Y) * s)','(hRμ : R + 1 < μ)','(hnmod : (2 * n) % μ = R + 1)','(hmy : ycoord m a = c)','(hg : g * g = 1 + delta a * c * c)','(i\' * c * c) * (i\' * c * c) + delta a = delta a * (f * f)','(haux :','absdiff (f * f * (T * c) + u)','13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1') :assert token in exact,token
power=t['ArithmeticPellPowerRecovery.lean'];assert 'theorem power_bound' in power and '(hX : 16≤X)' in power and '(hr : 2≤r)' in power and 'theorem projection_quotient' in power
assert 'theorem scalar_rank_window' in t['ArithmeticAdaptiveRankWindow2011.lean'] and 'theorem positive_parameter_solution' in t['ArithmeticPellFirstNorm.lean'] and 'theorem solution_index' in t['ArithmeticPellClassification.lean'] and 'theorem early_index_of_facts' in t['Compact44/FreeJEarlyIndex.lean']
gpath=D/'research/ordinary14-shifted-guard87-probe/candidate.json';assert sha(gpath)=='405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210';g=json.loads(gpath.read_text());rows={r[0]:r for r in g['source']}
for n,row in {'g31':['g31','-','g30','r'],'Z':['Z','+','g32','g33'],'I':['I','*','c2','i'],'g72':['g72','-','g71','Q'],'Fa':['Fa','-','y2','g82'],'guard':['guard','-','guard_base','bt_quotient']}.items():assert rows[n]==row
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(other)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C=json.loads(other.read_text());ports={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
assert ports['beta']>=46 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta'] and ports['K0']>=0
# Correct strong-factor mapping: i_prime=i, not Delta*i.
Delta,c,i,f=15,1,15,4;assert (i*c*c)**2==Delta*(f*f-1) and (i*c*c)**2+Delta==Delta*f*f and ((Delta*i)*c*c)**2+Delta!=Delta*f*f
checks=0
for q in range(3,101):
 for X in (1,2,7):
  for y0 in (1,2,5):
   Y=q**3*y0;H=3+4*Y*(X+1);d=math.gcd(H,q**5);assert d in (1,3) and q%d==0 and (q**5//d)%q**4==0 and q*q*Y*Y*(X*Y+Y)>H;checks+=1
# Pell projection χ_a(n)=2^n+a ψ_a(n) modulo 4a+3.
for a in range(1,15):
 x,y=1,0;Delta=a*a+4*a+3
 for n in range(10):
  assert (x-(1<<n)-a*y)%(4*a+3)==0
  x,y=(a+2)*x+Delta*y,x+(a+2)*y
print(json.dumps({'status':'PASS_CORRECTED_STANDARD_INTEGER_REPLAY','source_hypotheses_inspected':len(sources),'correct_strong_mapping':'i_prime=i','projection_and_gcd_controls':checks,'actual_port_bindings_checked':True,'scope':'external ordinary-natural decoder conditional on cited source theorem statements; no modified-graph Lean client, provider replay or PDF binding'},indent=2))
