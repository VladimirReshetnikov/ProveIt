import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
import circuit as base
VARS=['j','C','z','h','r','v','w','T','c','n','s']
def build(short=True):
 d=base.DAG(VARS);x={v:d.leaf('variable',v) for v in VARS};p={v:d.leaf('coefficient',v) for v in base.BASE_PORTS};j,C,z,h,r,v,w,T,c,n,s=[x[v] for v in VARS]
 J=6*j+1;qm=p['beta']*J;q=qm+1;q2=q*q;q3=q2*q
 W=12*w+4;X=q*W;Y=(2*v+1)*q3;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H;A=a+2
 F=(p['K0']+W)*C-z*qm;R=(q*(q-F)-C)*(q2-1)+(p['MC']+q*p['MF'])*J
 q24=4*q2;k=R+1+h*(q24*q2 if short else E);Yk=Y*k;eta=c-Yk
 Derr=(p['cone_A']*F-q)**2+(p['cone_B']*C-q)**2;Budget=k*k*(q2-Derr)-q24*eta*eta
 L=E*Yk;Dt=1+L*(L+k);D4=12*Budget-16;Pg=Dt*s;P=Dt+D4*Pg*Pg
 c2=c*c;Dm=1+Delta*c2;BP=Dm*P;U=r*c2*A;UBP=U*BP;strong=Delta*U*UBP;Df=strong+1;Q=Delta*strong;delta=Q-1
 V=Df*(c-R+4*UBP*T)-c;Cy=Q*V*V-1;K=X*(3*c-2*X)+2
 H2=H*H;H3=H2*H;zc=H*T+K;zc2=zc*zc;Ac=(zc2+3*H2)*(zc2*zc-19*H3);S=s*r*H;Z=S*n-Ac
 output=delta*Z*Z-S*S*BP*Df*Cy
 regs={k:v for k,v in locals().copy().items() if isinstance(v,base.Expr)};pack=base.export('product_main_guard11_'+('short' if short else 'native'),d,output,regs,dict(short=short,center='none',free_y=False))
 pack['coefficient_binding']='coefficients/BINDING.json';pack['exact_degree']=840 if short else 924
 deg=[]
 for row in pack['nodes']:
  deg.append((deg[row[1]]+deg[row[2]] if row[0]=='mul' else max(deg[row[1]],deg[row[2]])) if row[0] in ['mul','add','sub'] else int(row[0]=='variable'))
 pack['syntactic_degree_bound']=deg[-1]
 return pack
if __name__=='__main__':
 ps=[build(s) for s in [False,True]]
 for p in ps:(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
 metrics=[{k:p[k] for k in ['name','variable_count','operations','operation_counts','exact_degree','syntactic_degree_bound']} for p in ps]
 (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
