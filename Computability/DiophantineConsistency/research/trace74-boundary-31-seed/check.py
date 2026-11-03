#!/usr/bin/env python3
"""Finite arbitrary-port source seed; not a complete 74 graph zero."""
from hashlib import sha256
from pathlib import Path
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;D=H.parents[1]
G=D/'research/trace74-mask-coordinate-probe/candidate.json';SRC=D/'research/trace75-unscaled-reverse-data-prototype/Trace75UnscaledReverseData.lean';REC=D/'research/trace75-unscaled-reverse-data-prototype/observations/data-attempt02/terminal.json'
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
assert sha(G)=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
assert sha(SRC)=='ba0ef403b5834e1896ff1684bd6dbe1329a06b64947227eb76bd53ac0a0d8244'
assert sha(REC)=='1f552b8260ebae0c28db5e7ce6286d9163f148e9a217981f48685c31f307f7b5'
receipt=json.loads(REC.read_text());assert receipt['exit']==0 and receipt['reason'] is None and receipt['object_sha256']=='3ef7b82ef551100f48e1f932c0663f786eb4218f100ab8fa154890525baffc80'
# Pell x/y coordinate for x²-(a²−1)y²=1, at the usual base a.
def xy(a,n):
 x,y=1,0
 for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
 return x,y
s=int('20000007800000d980000fdc0000d61a0008b2a800487b7801f105800b29dfa03693d380e539ab83418be40a4f90521c8d8fa84557ca9893ee7d',16)
r=15;R=2*r+1;X=2**R;Y=8*s;P=X*Y*Y;A=Y*(X+1);first_x,first_y=xy(2*P+1,r+1);k=2*first_y
outer_c=xy(A+2,R)[1];eta=outer_c-k*Y;zeta=k-eta
c=xy(A+1,R)[1];eta_prime=c-k*Y;zeta_prime=k-eta_prime
H0=4*A-1;D0=X*Y;K=X*(3*c-2*X)+2;rho,rem=divmod(k-R-1,D0);kappa,hrem=divmod(K,H0)
assert s>0 and 0<eta<k and zeta>0 and 0<eta_prime<k and zeta_prime>0
assert 1+(P*k)*(P*k+k)==first_x*first_x
assert R%4==3 and 72*r<X+1 and rem==0 and hrem==0 and rho>=0 and kappa>0 and X<c
# Candidate rank and mask values, with an arbitrary finite trial at i=T=n=1.
g=json.loads(G.read_text());assert g['operations']==len(g['source'])==74
state={'beta':1,'K0':1,'MC':28,'MF':0,'J':1,'F':1,'C':1,'i':1,'T':1,'w':X//2,'s':s,'n':1,'eta':eta_prime,'zeta':zeta_prime}
for name,op,a,b in g['source']:
 a=a if type(a) is int else state[a];b=b if type(b) is int else state[b]
 state[name]=a+b if op=='+' else a-b if op=='-' else a*b
assert state['q']==2 and state['X']==X and state['Y']==Y and state['R']==R and state['Bt']==X//2
assert state['c']==c and state['k']==k and state['Dtau']==first_x*first_x
assert state['F']+state['C']==state['q'] and state[g['output']]!=0
z=state[g['output']];encoded=(b'-' if z<0 else b'+')+abs(z).to_bytes((abs(z).bit_length()+7)//8,'big')
for p,h in [(G,'dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'),(SRC,'ba0ef403b5834e1896ff1684bd6dbe1329a06b64947227eb76bd53ac0a0d8244')]:assert sha(p)==h
print(json.dumps({'status':'PASS_PARTIAL_SEED','ports':{'beta':1,'K0':1,'MC':28,'MF':0},'J':1,'F':1,'C':1,'R':R,'q':2,'X':X,'s_hex':hex(s),'s_bits':s.bit_length(),'first_index':r+1,'main_index':R,'source_interval_eta_positive':eta>0,'source_interval_zeta_positive':zeta>0,'actual_ordinate_eta_positive':eta_prime>0,'actual_ordinate_zeta_positive':zeta_prime>0,'pell_E_square':True,'offset_divisible_XY':rem==0,'K_divisible_H':hrem==0,'kappa_positive':kappa>0,'guard_fails_at_equality':True,'trial_i_T_n':1,'trial_graph_zero':False,'trial_output_signed_binary_sha256':sha256(encoded).hexdigest(),'graph_sha256':sha(G),'reverse_data_source_sha256':sha(SRC),'reverse_data_receipt_sha256':sha(REC),'scope':'exact finite arbitrary-port partial seed only; not a graph zero, fixed-port claim, Lean replay, or iPRA result'},sort_keys=True))
