from pathlib import Path
import hashlib,gzip,json,subprocess,sys
D=Path(__file__).resolve().parents[2];h=D/'research/trace74-fixed-bfs-scalar-boundary';graph=D/'research/trace74-mask-coordinate-probe/candidate.json';coef=D/'candidates/ten-positive-qcube-product-square/coefficients'
def sha(b):return hashlib.sha256(b).hexdigest()
assert sha((h/'check.py').read_bytes())=='66bccdcc129b730f4c46befc53d26e7db9baa320da3afe3f8ee9834ff0296772' and sha((h/'observation.json').read_bytes())=='2bc1bc720ff7efc6ecb29ddaf823705fcae730415eeceaaedb0cbcff2e0e843b' and sha(graph.read_bytes())=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353';g=json.loads(graph.read_text());assert len(g['source'])==g['operations']==74
z=subprocess.run([sys.executable,'-I','-S','-B',str(h/'check.py')],capture_output=True,text=True);assert z.returncode==0 and not z.stderr and json.loads(z.stdout)==json.loads((h/'observation.json').read_text())
values={}
for name in ('beta','MC','MF','K0'):
 spec=g['coefficient_binding']['ports'][name];blob=(coef/spec['file']).read_bytes();assert sha(blob)==spec['parent_gzip_sha256'];raw=gzip.decompress(blob);assert sha(raw)==spec['raw_sha256'];v=int.from_bytes(raw,'little');assert v.bit_length()==spec['bits'];values[name]=v
B=values['beta'];L=values['MC'];M=values['MF'];K0=values['K0'];d=67*8807;Q=B+1;H=M-B;assert B>=31 and Q==2**d and 0<=L<B and 0<=H<B and Q%4==0 and L%4==2
rows={r[0]:r[1:] for r in g['source']};targets={'R','c','Y','G'};anc=set();todo=list(targets)
while todo:
 n=todo.pop()
 if n in anc or n not in rows:continue
 anc.add(n);_,a,b=rows[n]
 for v in (a,b):
  if isinstance(v,str):todo.append(v)
assert 'K0' not in {v for n in anc for v in rows[n][1:]}
def evalrows(initial):
 v=initial.copy()
 for n,op,a,b in g['source']:
  if n not in anc:continue
  x=v[a] if isinstance(a,str) else a;y=v[b] if isinstance(b,str) else b;v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
v={'beta':B,'K0':K0,'MC':L,'MF':M,'J':1,'F':3,'C':Q-3,'w':1,'s':1,'i':1,'T':1,'n':1,'eta':1,'zeta':1};assert all(v[x]>0 for x in g['witnesses']) and v['F']+v['C']==Q
r=evalrows(v);R=r['R'];assert r['G']==(Q-1)*(Q-3) and R==Q**4-4*Q**3+3*Q**2+3*Q+L-3+Q*H and R%4==3 and 3*Q<R and R>=d
margin=Q**4-(R+Q**3+Q+1);assert margin==3*Q**3-3*Q**2-4*Q+2-L-Q*H and margin>=3*Q**3-4*Q**2-5*Q+4>0
v['s']=R+1;r=evalrows(v);assert r['R']==R and r['Y']==Q**3*(R+1) and r['c']==2*r['Y']+1 and 2*R<r['c']
a=json.loads((h/'observation.json').read_text());assert a['status']=='PASS_SCALAR_ONLY' and a['q_exponent']==d and a['rank_bits']==R.bit_length() and a['rank_mod_4']==3 and a['guard']=='F+C=q' and a['c_gt_2rank'];print('PASS four pinned parent coefficient payloads, independent JSON R/c cones, positive scalar boundary, phase and rank/size inequalities; no full output')
