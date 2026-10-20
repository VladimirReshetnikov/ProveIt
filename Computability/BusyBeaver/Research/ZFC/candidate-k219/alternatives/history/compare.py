from pathlib import Path
import hashlib,json
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
A=Path('/tmp/zfc-intake187/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20')
OUT=Path(__file__).resolve().parent
B=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k219'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 t={};start=[]
 for l in p.read_text().splitlines():
  if l.startswith('#! start '):start.append(int(l.split()[-1]))
  elif l and not l.startswith('#'):
   q,b,w,d,z=l.split();k=int(q),int(b);assert k not in t;t[k]=int(w),d,int(z)
 assert start==[0];return t

def encode(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n' for(q,b),(w,d,z)in sorted(t.items()))).encode()
base=read(B/'k219.native.tm');row=read(B/'variant-row157/k219-row157.native.tm')
mp={301:102,302:120}
norm=lambda t:{(mp.get(q,q),b):(w,d,mp.get(z,z))for(q,b),(w,d,z)in t.items()}
b=norm(base);r=norm(row)
res={'baseline':{'path':str(B/'k219.native.tm'),'sha256':sha(B/'k219.native.tm')},'row157_patch':[[*k,list(b[k]),list(r[k])]for k in b if b[k]!=r[k]],'normalization':mp,'variants':{}}
(OUT/'normalized-baseline.tm').write_bytes(encode(b));(OUT/'normalized-row157.tm').write_bytes(encode(r))
variants={n:read(A/f'machine/{n}/k219.native.tm')for n in ['zero_terminal','retagged','composed']}
for n,t in variants.items():
 assert set(t)==set(b) and len(t)==438
 delta=[[*k,list(b[k]),list(t[k])]for k in sorted(b)if t[k]!=b[k]]
 assert all(b[k]==t[k]for k in b if b[k]!=r[k]),'row157 conflict'
 x=dict(t)
 for k in b:
  if b[k]!=r[k]:x[k]=r[k]
 d=OUT/(n+'-row157');d.mkdir(exist_ok=True)
 (d/'table.native.tm').write_bytes(encode(x))
 res['variants'][n]={'original_path':str(A/f'machine/{n}/k219.native.tm'),'sha256':sha(A/f'machine/{n}/k219.native.tm'),'patches':delta,'working_states':len({q for q,bit in t}),'row157_stack_path':str(d/'table.native.tm'),'row157_stack_sha256':sha(d/'table.native.tm')}
z,rt,c=[variants[n]for n in ['zero_terminal','retagged','composed']]
u=dict(z)
for k in b:
 if rt[k]!=b[k]:
  assert z[k]==b[k];u[k]=rt[k]
res['literal_zero_retag_union_vs_composed']=[[*k,list(u[k]),list(c[k])]for k in b if u[k]!=c[k]]
(OUT/'literal-zero-retag-union.tm').write_bytes(encode(u))
for n,t in variants.items():
 res['variants'][n]['incoming_139']=[[*k,list(v)]for k,v in t.items()if v[2]==139]
 res['variants'][n]['incoming_157']=[[*k,list(v)]for k,v in t.items()if v[2]==157]
res['status']='EXACT_LITERAL_COMPARISON_PASS'
(OUT/'comparison.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
