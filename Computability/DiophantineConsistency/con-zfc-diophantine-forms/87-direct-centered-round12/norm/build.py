"""Build the complete H1868 norm-saturated ordinary polynomial from inert data."""
from pathlib import Path
import json,gzip,hashlib,math,sys
MODE=sys.argv[1] if len(sys.argv)>1 else "center1"
if MODE not in ("polar","center0","center1","center2"): raise ValueError(MODE)
from circuit import Circuit,horner
ROOT=Path(__file__).resolve().parent;KAPPA=2134940
code=json.loads((ROOT/'data/code.json').read_text());kernel=json.loads((ROOT/'data/kernels.json').read_text())
weights=code['weights'];targets0=code['targets_by_row'];W=max(weights);HH=max(t['exponent']+layer['degree']*W for layer in kernel['kernels'] for t in layer['terms'])
d=Circuit();A,M,S,P,c,N=d.add,d.mul,d.sub,d.pow,d.c,d.save
names=['t','g0','c0','k0','l','w','x','y','z','m'];v={s:d.leaf('variable',name=s)for s in names}
b=N('b',A(M(c(6),v['t']),c(4)));g=N('g',M(b,v['g0']));k=N('twice_k',M(b,A(M(c(6),v['k0']),c(4))))
base=N('base',M(d.leaf('fixed',name='radix'),P(b,2)))
required={1,W,W+1,HH+1,W+HH+2,HH+2*W+9}
for exponents in [weights,targets0]+[[term['exponent']for term in layer['terms']]for layer in kernel['kernels']]:
 es=sorted(set(exponents));required.add(es[0]);required.update(y-x for x,y in zip(es,es[1:]))
todo=required-{0};plan={}
while len(todo)>1:
 a=max(todo);todo.remove(a);b0=max(todo);pairs=[(abs(2*x-a),x,a-x)for x in todo if a-x in todo]
 if pairs:_,x0,y0=min(pairs)
 elif 2*b0<a:x0,y0=(a//2,a//2)if a%2==0 else(a-1,1)
 else:x0,y0=b0,a-b0
 plan[a]=(x0,y0);todo.update((x0,y0))
optimized=json.loads((ROOT/'OPTIMIZED_POWER_PLAN.json').read_text())
if optimized['required']!=sorted(required-{0}):raise RuntimeError('power-plan target mismatch')
plan={int(k):tuple(v) for k,v in optimized['plan'].items()}
for power,(left,right) in plan.items():
 if left<=0 or right<=0 or left+right!=power or max(left,right)>=power:raise RuntimeError('invalid shared power identity')
d.power_plans[base]=plan
ell=N('ell',horner(d,base,[(w,c(1))for w in weights]));recipes={};sig={};kernels=[]
for layer in kernel['kernels']:
 terms=[]
 for term in layer['terms']:
  recipe=term['coefficient'];key=json.dumps(recipe,sort_keys=True)
  if len(recipe)==1 and not any(recipe[0]['powers']):node=c(recipe[0]['coefficient'])
  else:
   if key not in sig:sig[key]='c%03d'%len(sig);recipes[sig[key]]=recipe
   node=d.leaf('fixed',name=sig[key])
  terms.append((term['exponent'],node))
 kernels.append(N('Dcode'+str(layer['degree']),horner(d,base,terms)))
word=N('word',A(ell,g));coded=N('coded',A(kernels[0],M(word,A(kernels[1],M(word,kernels[2])))))
top=P(base,W);n0=N('n0',P(base,W+1));nn=N('nn',P(base,W+HH+2))
targets=N('targets',horner(d,base,[(e,c(1))for e in targets0]))
mask=N('mask',S(S(n0,c(1)),M(S(b,c(1)),ell)))
tc0=N('tc_original',A(mask,M(S(base,c(2)),targets,n0)));tc=N('tc',S(tc0,c(2)))
jc=N('jc',A(M(c(2),coded),targets));sc=N('sc',A(g,M(jc,n0)))
X=N('X',S(S(M(nn,A(sc,tc,c(1))),sc),c(1)))
Y=N('Y',M(d.leaf('fixed',name='threshold'),P(base,HH+2*W+9),b));cap=N('cap',M(b,top))
L=N('L',M(v['l'],Y));u=N('halfU',M(L,X));U=N('U',M(c(2),u));V=N('V',M(c(4),g,v['w'],Y));ww=N('W',M(b,v['w']))
uv=N('uv',M(u,V));ha=N('halfA',A(u,uv));a=N('A',M(c(2),ha));bb=N('B1',A(M(c(2),X),c(1)))
C=N('C',S(M(c(6),v['c0']),c(1)));ph=N('Phalf',M(U,uv));pn=N('P',M(c(2),ph))
K=N('K',A(X,c(1),M(k,S(ph,c(1)))));K2=P(K,2)
ss=N('S',S(M(c(2),a),c(5)));tt=N('T',A(M(ww,S(M(c(3),C),M(c(2),ww))),c(2)))
Q=N('Q',A(M(S(P(ph,2),c(1)),K2),c(1)))
cap3=P(cap,3);g2=P(g,2);CKL=N('CKL',S(C,M(K,L)))
Delta=N('Delta',S(M(g,S(cap,g),K2),M(P(cap,2),P(CKL,2))))
xi=N('xi',M(v['z'],v['x']));C2=P(C,2);A2m4=S(P(a,2),c(4));D=N('D',A(M(A2m4,C2),c(4)));E0=N('E0',M(C2,xi));E=N('E',M(E0,D))
E2=N('E2',M(E0,E))
Fm1=N('Fm1',M(c(4),A2m4,E2));F=N('F',A(Fm1,c(1)));G=N('G',S(M(S(ha,c(1)),Fm1),c(1)))
Omega=N('Omega',M(c(16),E));H=N('H',A(C,M(F,A(S(bb,C),M(Omega,v['y'])))))
I=N('I',A(M(S(P(G,2),c(1)),P(H,2)),c(1)))
Sigma=N('Sigma',M(xi,P(ss,5)));rho=N('rho',A(tt,M(ss,v['y'])));rho2=P(rho,2);ss2=P(ss,2)
Theta=N('Theta',M(S(M(rho,S(rho2,ss2)),M(ss,ss2)),A(rho2,M(c(23),ss2))))
r=N('r',M(b,Q));guard=N('guard',A(r,M(S(M(c(9),Delta),c(3)),P(M(r,v['z']),2))))
lucas=N('lucas',M(D,F,I));center=N('center',S(M(Sigma,v['m']),Theta));sigma2=P(Sigma,2)
# Polynomial square completion; the translated coordinate is m+R.
R0=N('R0',M(c(2),a,E) if MODE=='center0' else M(c(2),a,E0,S(D,M(c(2),C2))))
R=N('R',M(R0,G,H))
J=N('J',S(D,M(c(16),P(E,2))) if MODE=='center0' else A(D,M(c(16),P(E0,2),S(M(S(M(c(3),C2),c(4)),D),M(c(4),C2,S(C2,c(1)))))))
rem=N('remainder',S(M(J,P(G,2),P(H,2)),M(D,F,S(P(H,2),c(1)))))
if MODE=='center2':
    C2m1=S(C2,c(1)); Ex2=P(E0,2)
    F0=N('F0',A(c(1),M(c(64),Ex2,C2m1)))
    Om0=N('Om0',M(c(-64),E0,C2m1))
    HH0=N('H0',A(C,M(F0,A(S(bb,C),M(Om0,v['y'])))))
    GH0=N('GH0',M(c(-1),F0,HH0))
    Jf=N('Jf',M(E0,A(M(C2,P(a,2)),c(4),M(c(-8),C2))))
    Warg=A(S(bb,C),M(Omega,v['y']))
    Qdiv=N('Qdiv',S(M(S(M(c(2),P(ha,2)),c(2)),E,H),M(a,A(M(Jf,A(C,M(A(F,F0),Warg))),M(c(4),C2,P(F0,2),v['y'])))))
    LL=N('LL',A(c(1),M(c(16),Ex2,S(M(c(3),C2),c(4)))))
    J0=N('J0',S(M(c(-4),C2m1),M(c(256),Ex2,P(C2m1,2))))
    GH=N('GH',M(G,H));correction=N('correction',M(LL,Qdiv))
    R=N('Rfinal',A(R,correction))
    rem=N('remainder_final',S(S(A(M(J0,P(GH,2)),M(C2,LL,a,GH,S(M(a,GH0),M(c(4),xi,S(c(4),M(c(6),C2)),Qdiv)))),P(correction,2)),M(D,F,S(P(H,2),c(1)))))
translated=N('translated_center',A(center,M(Sigma,R)))
inner=N('inner',A(P(center,2),M(c(2),Sigma,R,center),M(sigma2,S(guard,rem))))
out=N('F10',S(P(inner,2),M(c(4),sigma2,guard,P(translated,2))))
if MODE=='polar':
    center2=P(center,2)
    inner=N('inner',A(center2,M(sigma2,S(guard,lucas))))
    out=N('F10',S(P(inner,2),M(c(4),sigma2,guard,center2)))
body=d.finish(out);body.update(schema='round12-short-guard-polynomial-centered-norm-H1868-v1',domain='Z',variables=names,source_files=['data/source.json','data/code.json','data/kernels.json'],fixed_recipes=recipes,base_exponent=KAPPA,threshold_exponent=16*KAPPA-23,W=W,H=HH,degree_formula={'polar':'76*deg(A)+140','center0':'72*deg(A)+140','center1':'68*deg(A)+140','center2':'66*deg(A)-456'}[MODE],proof_status='Ordinary mathematical reduction; no new kernel certificate.',count_convention='Fixed integer leaves cost0; all binary operations including scalar multiplication and squaring cost1; shared reuse free.')
(ROOT/('integer10_'+MODE+'.json')).write_text(json.dumps(body,separators=(',',':'))+'\n')
# Complete actual numeral payloads. No implicit MRDP parameter is left unspecified.
ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{name}.bin.gz').read_bytes()),'little')for name in ['beta','K','MC','MF_source']]
fixed={name:sum(row['coefficient']*math.prod(v**e for v,e in zip(ports,row['powers']))for row in rows)for name,rows in recipes.items()}
fixed.update(radix=2**KAPPA,threshold=2**(16*KAPPA-23));(ROOT/'fixed').mkdir(exist_ok=True);manifest={}
for name in sorted({n['name']for n in body['nodes']if n['kind']=='fixed'}):
 v=fixed[name];raw=(b'\x01'if v<0 else b'\x00')+abs(v).to_bytes((abs(v).bit_length()+7)//8 or 1,'little');gz=gzip.compress(raw,mtime=0);fn='fixed/'+name+'.signed-le.gz';(ROOT/fn).write_bytes(gz)
 manifest[name]={'file':fn,'encoding':'sign byte, then unsigned little-endian magnitude','bit_length':abs(v).bit_length(),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_sha256':hashlib.sha256(gz).hexdigest()}
(ROOT/'FIXED_COEFFICIENTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
metrics={k:v for k,v in body.items()if k not in ('nodes','fixed_recipes','named_nodes')};metrics['fixed_payload_compressed_bytes']=sum((ROOT/v['file']).stat().st_size for v in manifest.values());(ROOT/('METRICS_'+MODE+'.json')).write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
