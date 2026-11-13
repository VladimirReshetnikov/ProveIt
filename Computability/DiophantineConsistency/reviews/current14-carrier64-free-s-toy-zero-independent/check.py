from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-carrier64-free-s-toy-zero'
pins={'README.md':'b83bf8af3ff4af68b6a2f253b2eaaeeae351a15d74f0147d780f9a90e7610cd8','check.py':'364eabe29ba99a665337861ba532aa3b6117a4b8f803d686b945d751049a6458','result.json':'7fc09a7de452817f65b877dfdfd2c4d7ac1cf9f1440fbbf1b0c1212874656e26'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
g=json.loads((root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json').read_text());rows=g['source']; assert rows[51]==['normalized_S','*','i','Dc2']; assert rows[52]==['normalized_S2','*','normalized_S','normalized_S']
new=[[r[0],r[1],*['i' if x=='normalized_S' else x for x in r[2:]]] for r in rows if r[0]!='normalized_S']
def live(rows):
 by={r[0]:r[2:] for r in rows};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in by and x not in seen:seen.add(x);todo.extend(by[x])
 return seen
assert len(live(rows))==65 and len(live(new))==64
beta,K,MC,MF=31,9,14,46;q=beta+1;F,alpha,J=1,14,1;C=q-F-alpha;gap=beta*(q-F)+alpha
R=gap*(q*q-1)+(MC+q*MF)*J;N=(R-1)//2
assert C==17 and gap==975 and R==998911 and R%4==3 and N.bit_count()-1==15 and q**3==2**15
wmod=pow(2,R-5,beta);assert wmod==2 and ((K+wmod)*C-F)%beta==0
# Exact small instance of the same free-S Pell/Chebyshev congruences.
A=3;idx=3;delta=A*A-1;c=4*A*A-1;D=4*A*A*A-3*A;S=delta*c;f=D;V=4*S*S-3;y=4*S*S-1
assert f*f-delta*c*c==1 and delta*f*f-S*S==delta
assert (V+c)%(f*f)==0 and (V+idx)%c==0 and (f*f-1)%c==0
T,rem=divmod(V+c+f*f*idx,c*f*f);assert rem==0 and T>0 and V==f*f*(c*T-idx)-c
assert S*S*(V*V-y*y)+y*y==1
print(json.dumps({'status':'PASS_SYMBOLIC_EXTERNAL_REVIEW','toy_ports':[31,9,14,46],'candidate_live_gates':64,'actual_pell_witness_expanded':False,'scope':'toy-port candidate zero and same-other-coordinate strong-factor obstruction only; no actual-port, Lean or unrestricted nonequivalence'},indent=2))
