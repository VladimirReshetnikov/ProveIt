from pathlib import Path
from hashlib import sha256
import json
root=Path(__file__).resolve().parents[2];h=root/'research/trace74-boundary-31-seed';graph=root/'research/trace74-mask-coordinate-probe/candidate.json';src=root/'research/trace75-unscaled-reverse-data-prototype/Trace75UnscaledReverseData.lean';receipt=root/'research/trace75-unscaled-reverse-data-prototype/observations/data-attempt02/terminal.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(h/'check.py')=='d46fcda0011422f6bd534bb45260f8d461f537a231ce9dcc8d1052107bbf21f1' and sha(h/'observation.json')=='bcaf04a0f6651682c5e016748a90dbcdcd3b15bf5b9a14dea62530155238dd93'
assert sha(graph)=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353' and sha(src)=='ba0ef403b5834e1896ff1684bd6dbe1329a06b64947227eb76bd53ac0a0d8244' and sha(receipt)=='1f552b8260ebae0c28db5e7ce6286d9163f148e9a217981f48685c31f307f7b5'
# Independent second-order ordinary Pell ordinate recurrence (not the seed's xy loop).
def y(a,n):
 u,v=0,1
 for _ in range(n):u,v=v,2*a*v-u
 return u
s=int('20000007800000d980000fdc0000d61a0008b2a800487b7801f105800b29dfa03693d380e539ab83418be40a4f90521c8d8fa84557ca9893ee7d',16);r=15;R=31;X=1<<R;Y=8*s;P=X*Y*Y;A=Y*(X+1);firstbase=2*P+1;k=2*y(firstbase,16);tau=y(firstbase,17)-firstbase*y(firstbase,16);cs=y(A+2,R);c=y(A+1,R);eta=cs-k*Y;ep=c-k*Y;H=4*A-1;K=X*(3*c-2*X)+2
assert s>0 and s.bit_length()==462 and R==2*r+1 and X==2**R and R%4==3 and 72*r<X+1
assert 0<eta<k and 0<k-eta and 0<ep<k and 0<k-ep and 1+(P*k)*(P*k+k)==tau*tau
assert (k-R-1)%(X*Y)==0 and K%H==0 and K//H>0 and X<c
# Pinned Lean recurrence advances by ordinary base b+2, so the first seed uses b=2(P-1)+1 and the outer seed uses b=A.
assert (2*(P-1)+1)+2==firstbase and (A-1)+2==A+1
g=json.loads(graph.read_text());assert g['operations']==len(g['source'])==74
v={'beta':1,'K0':1,'MC':28,'MF':0,'J':1,'F':1,'C':1,'i':1,'T':1,'w':X//2,'s':s,'n':1,'eta':ep,'zeta':k-ep}
for name,op,left,right in g['source']:
 assert name not in v and op in ('+','-','*');a=left if type(left) is int else v[left];b=right if type(right) is int else v[right];v[name]={'+' : lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
assert v['q']==2 and v['X']==X and v['Y']==Y and v['R']==31 and v['Bt']==X//2 and v['c']==c and v['k']==k and v['Dtau']==tau*tau and v['F']+v['C']==v['q']
z=v[g['output']];assert z!=0;encoded=(b'-' if z<0 else b'+')+abs(z).to_bytes((abs(z).bit_length()+7)//8,'big');obs=json.loads((h/'observation.json').read_text());assert sha256(encoded).hexdigest()==obs['trial_output_signed_binary_sha256'] and obs['trial_graph_zero'] is False
assert 28>=1 and obs['ports']=={'beta':1,'K0':1,'MC':28,'MF':0}
print('PASS independent second-order Pell recurrence, intervals/norm/divisibilities/rank, all 74 trial rows and signed output digest; trial is nonzero and fixed-port bound fails')
