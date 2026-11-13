from pathlib import Path
import hashlib,json,subprocess,sys,math
root=Path(__file__).resolve().parents[2];d=root/'research/current14-carrier64-free-pell-gap-toy-zero'
pins={'README.md':'c6f69da619cc455419a73e09263da67e796915d1d352198a20dbd61c18863ddf','check.py':'0a28c6331a0f8132e23e92852bb3b8acfdffefee639a3cf2dc9c17bb68e58850','result.json':'24c24d8afa899a369e1855f09991909a2d32564463a9722726d9654c792ae02a'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
# Prior reviewed READMEs were later amended only with review status/links. Reverse those exact edits in memory and compare the original reviewed hashes; leave earlier immutable checker scripts untouched.
for name,oldhash,review in [('current14-carrier64-free-s-toy-zero','b83bf8af3ff4af68b6a2f253b2eaaeeae351a15d74f0147d780f9a90e7610cd8','current14-carrier64-free-s-toy-zero-independent'),('current14-carrier65-positive-v','9af4bb4a9b9870ca8addf9d0fd8aab8e5c5654f277ede528b662d4558afa0d90','current14-carrier65-positive-v-independent')]:
 q=root/'research'/name;readme=(q/'README.md').read_text();tail=f'\nIndependent external review is recorded in\n`../../reviews/{review}/`.\n';assert readme.endswith(tail);readme=readme[:-len(tail)]
 if name=='current14-carrier64-free-s-toy-zero':readme=readme.replace('This has passed independent external review; it is not a Lean/PDF result,','This is submitted for independent review, not a Lean/PDF result,')
 assert hashlib.sha256(readme.encode()).hexdigest()==oldhash
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(q/'check.py')])==(q/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());rows=g['source'];assert [r for r in rows if 'y' in r[2:]]==[['y2','*','y','y']] and [r for r in rows if 'V' in r[2:]]==[['V2','*','V','V']] and [r for r in rows if 'T' in r[2:]]==[['cT','*','c','T']]
assert rows[53:58]==[['V2','*','V','V'],['y2','*','y','y'],['V2minusY2','-','V2','y2'],['aux_product','*','normalized_S2','V2minusY2'],['Na','+','aux_product','y2']]
new=[]
for row in rows:
 if row[0] in ('y2','V2minusY2'):continue
 if row[0]=='aux_product':new.append(['S2minus1','-','normalized_S2',1]);row=['aux_product','*','S2minus1','y']
 if row[0]=='Na':row=['Na','-','V2','aux_product']
 new.append(row)
def live(rs):
 by={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in by and x not in seen:seen.add(x);todo.extend(by[x])
 return seen
assert len(rows)==len(live(rows))==65 and len(new)==len(live(new))==64 and len(g['witnesses'])==14
# Independent exact small Pell-ring + CRT construction, not the huge claimed witness.
A,R=3,3;delta=A*A-1;c=4*A*A-1;D=4*A**3-3*A;f,L=1,0
for _ in range(70):f,L=D*f+delta*c*L,c*f+D*L
assert L%(c*c)==0 and f*f-delta*L*L==1 and f%A in (1,A-1)
S=delta*L;M=S*S-1;mods=[M,c,f*f];assert all(math.gcd(mods[i],mods[j])==1 for i in range(3) for j in range(i));residues=[1,-R,-c];period=math.prod(mods);V=sum((b%m)*(period//m)*pow(period//m,-1,m) for b,m in zip(residues,mods))%period;V+=period
for _ in range(20):
 t,rem=divmod(V*V-1,M);assert rem==0 and t>0;T,rem=divmod(V+c+f*f*R,c*f*f);assert rem==0 and T>0 and V==f*f*(c*T-R)-c and V*V-M*t==1
 if math.isqrt(V*V+t)**2!=V*V+t:break
 V+=period
else:raise AssertionError('finite CRT control did not find a nonsquare')
print(json.dumps({'status':'PASS_SYMBOLIC_EXTERNAL_REVIEW','candidate_live_gates':64,'illustrative_crt_nonsquare':True,'actual_toy_witness_expanded':False,'scope':'toy-port symbolic zero and same-other-coordinate obstruction only; no current-port, Lean or unrestricted nonequivalence'},indent=2))
