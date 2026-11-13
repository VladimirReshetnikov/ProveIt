from pathlib import Path
import hashlib,json,subprocess,sys,math
root=Path(__file__).resolve().parents[2];d=root/'research/current14-carrier63-free-u-toy-zero'
pins={'README.md':'502fa652b31ad52ea670676c60b716d14237084b7e10a6b854bf6925a25dd424','check.py':'6d4c6af889f28a4a40d32e0e610cf60db3d1a6ff75dc09c7ef77f7ca0c66be8b','result.json':'2de1e0ca330accfda4f5acc0b7f2d45fd79a393e2f490df26b314c27750c8005'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
# Reconstruct exactly the old independently audited README bytes after status-only amendments.
for name,oldhash,review in [('current14-carrier64-free-s-toy-zero','b83bf8af3ff4af68b6a2f253b2eaaeeae351a15d74f0147d780f9a90e7610cd8','current14-carrier64-free-s-toy-zero-independent'),('current14-carrier65-positive-v','9af4bb4a9b9870ca8addf9d0fd8aab8e5c5654f277ede528b662d4558afa0d90','current14-carrier65-positive-v-independent')]:
 q=root/'research'/name;readme=(q/'README.md').read_text();tail=f'\nIndependent external review is recorded in\n`../../reviews/{review}/`.\n';assert readme.endswith(tail);readme=readme[:-len(tail)]
 if name=='current14-carrier64-free-s-toy-zero':readme=readme.replace('This has passed independent external review; it is not a Lean/PDF result,','This is submitted for independent review, not a Lean/PDF result,')
 assert hashlib.sha256(readme.encode()).hexdigest()==oldhash and subprocess.check_output([sys.executable,'-I','-S','-B',str(q/'check.py')])==(q/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());rows=g['source'];assert rows[47:50]==[['cT','*','c','T'],['cTminusR','-','cT','R'],['f2inner','*','f2','cTminusR']] and [r for r in rows if 'T' in r[2:]]==[['cT','*','c','T']]
new=[]
for row in rows:
 if row[0] in ('cT','cTminusR'):continue
 if row[0]=='f2inner':row=['f2inner','*','f2','T']
 new.append(row)
def live(rs):
 by={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in by and x not in seen:seen.add(x);todo.extend(by[x])
 return seen
assert len(rows)==len(live(rows))==65 and len(new)==len(live(new))==63 and len(g['witnesses'])==14
# Independent exact small controls: exponentiate Pell pairs directly, including exact quotient by S after modular reduction.
def mul(x,y,D,mod):return ((x[0]*y[0]+D*x[1]*y[1])%mod,(x[0]*y[1]+x[1]*y[0])%mod)
def power(x,n,D,mod):
 out=(1,0)
 while n:
  if n&1:out=mul(out,x,D,mod)
  x=mul(x,x,D,mod);n//=2
 return out
controls=[]
for A in (2,4):
 R=3;delta=A*A-1;D=4*A**3-3*A;c=4*A*A-1;f,L=1,0
 for _ in range(c):f,L=D*f+delta*c*L,c*f+D*L
 assert f*f-delta*L*L==1 and L%(c*c)==0 and f%D==0 and (f//D)%2==1
 m=R*c;Q=f//D;t=2*m*Q-R;assert t>0 and t%4==3 and c>2*R
 # The anti-period is checked directly in the A-unit ring, independently of the auxiliary Chebyshev recurrence.
 assert power((A,1),t,delta,f*f)[1]==c%(f*f)
 S=delta*L;mod=f*f*c;trace=power((S,1),t,S*S-1,S*mod)[0];assert trace%S==0;Vmod=(trace//S)%mod
 assert Vmod%(f*f)==(-c)%(f*f) and Vmod%c==R and ((Vmod+c)//(f*f)+R)%c!=0
 controls.append({'A':A,'c':c,'anti_period_checked':True,'auxiliary_congruences_checked':True})
print(json.dumps({'status':'PASS_SYMBOLIC_EXTERNAL_REVIEW','candidate_live_gates':63,'small_controls':controls,'actual_toy_witness_expanded':False,'scope':'toy-port symbolic zero and same-other-coordinate obstruction only; no current-port, Lean or unrestricted nonequivalence'},indent=2))
