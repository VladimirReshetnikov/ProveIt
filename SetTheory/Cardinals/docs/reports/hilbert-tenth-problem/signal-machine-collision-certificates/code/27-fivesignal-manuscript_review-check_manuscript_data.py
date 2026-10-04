"""New read-only exact algebra and static table binding check for Report57.

This does not import or run any construction/audit/release program, choose a
physical next collision, or evolve the saved JSON as a machine. Phase templates
below are independently transcribed from the proved primitive grammar.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, json, re, hashlib
import sympy as s

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--release-root',required=True,type=Path)
parser.add_argument('--output-dir',required=True,type=Path)
args=parser.parse_args()
ROOT=args.release_root.resolve(strict=True)
if args.output_dir.exists() or args.output_dir.is_symlink():
    raise ValueError('Output must be an exclusive brand-new directory')
OUT=args.output_dir.resolve()
if OUT.is_relative_to(ROOT):
    raise ValueError('Output must be outside the reviewed release tree')
if not __debug__:
    raise ValueError('Assertions must remain enabled; do not use -O')
OUT.mkdir(parents=True,exist_ok=False)
checks=[]
def ck(name, condition):
    assert condition, name
    checks.append(name)
def eq(a,b): return s.expand(a-b)==0
def rat_tex(x):
    x=x.strip().strip('$')
    m=re.fullmatch(r'(-?)\\frac\{(\d+)\}\{(\d+)\}',x)
    return F((-1 if m[1] else 1)*int(m[2]),int(m[3])) if m else F(x)
def label(x): return re.fullmatch(r'\\texttt\{(.+)\}',x.strip())[1].replace(r'\_','_')

D,X,Y=s.symbols('D X Y')
qq=s.Rational
x0=D/3+X; y0=2*D/3+Y
guards=[]
def block(x,y,reflected=False):
    z,t=(D-x,D-y) if reflected else (y,x)
    c,d=(qq(2,5),qq(-4,15)) if reflected else (qq(-1,4),qq(1,6))
    pts=[t,t+c*z,t+c*z+d*D,t+2*c*z+d*D,t+2*c*z+2*d*D]
    guards.extend([s.expand(z),s.expand(D-z)])
    for v in pts: guards.extend([s.expand(v),s.expand(z-v)])
    clock=s.S(0)
    for start,refl,par in [(pts[0],z,c),(pts[1],D,d),(pts[2],z,c),(pts[3],D,d)]:
        clock+=2*(2-par)/(1-par)*start+2*refl
    return ((x,s.expand(D-pts[-1])) if reflected else (s.expand(pts[-1]),y)),s.expand(clock)
(x1,y1),c1=block(x0,y0)
(x2,y2),c2=block(x1,y1,True)
(xr,yr),c3=block(x2,y2)
ck('rotation endpoint x',eq(xr,D/3+3*X/5-4*Y/5))
ck('rotation endpoint y',eq(yr,2*D/3+4*X/5+3*Y/5))
ck('A block clock',eq(c1,16*x0-y0/5+16*D/3))
ck('B block clock',eq(c2,qq(1016,57)*(D-y1)+qq(2972,285)*(D-x1)+qq(1388,855)*D))
ck('36 derived guard rows',len(guards)==36)
guardlines=(ROOT/'science/construction/GUARDS.txt').read_text().splitlines()[1:]
for i,(formula,line) in enumerate(zip(guards,guardlines),1):
    expression=line.split(': ',1)[1]
    ck(f'guard lexical whitelist {i}',re.fullmatch(r'[DXY0-9+*/ -]+',expression) is not None)
    parsed=s.sympify(expression,locals={'D':D,'X':X,'Y':Y})
    ck(f'guard source row {i}',eq(formula,parsed))
dist=[]
for f in guards:
    a,b,c=[f.coeff(v) for v in (D,X,Y)]
    ck(f'positive constant guard {len(dist)+1}',a>0)
    dist.append(a*a/(b*b+c*c))
texrows=[l for l in (ROOT/'assets/guards.tex').read_text().splitlines() if re.match(r'^\d+ & ',l)]
ck('36 printed guards',len(texrows)==36)
for i,(f,l) in enumerate(zip(guards,texrows)):
    vals=l.split('&'); coeff=[rat_tex(v) for v in vals[2:5]]
    ck(f'appendix guard coefficients {i+1}',coeff==[f.coeff(v) for v in (D,X,Y)])
    printed=rat_tex(vals[5].split(r'\\')[0])
    ck(f'appendix guard distance {i+1}',printed==dist[i])
ck('block distance minima',[min(dist[k:k+12]) for k in (0,12,24)]==[qq(1,45),qq(4,1845),qq(4,153)])
ck('unique row18 minimum',[i+1 for i,d in enumerate(dist) if d==min(dist)]==[18])
a,b,c=[guards[17].coeff(v) for v in (D,X,Y)]
p=s.Matrix([-a*b/(b*b+c*c),-a*c/(b*b+c*c)])
ck('contact p',p==s.Matrix([qq(4,205),qq(-26,615)]))
R=s.Matrix([[qq(3,5),qq(-4,5)],[qq(4,5),qq(3,5)]])
Q=s.Matrix([[1,1,1],[qq(2,3),qq(-1,3),qq(-1,3)],[qq(1,3),qq(1,3),qq(-2,3)]])
M=s.Matrix([[7,-2,10],[14,11,-10],[-6,6,15]])/30
N=s.diag(qq(1,2),R/2)
ck('conjugacy',Q*M*Q.inv()==N)
ck('radius',p.dot(p)==qq(4,1845))
ck('forward boundary point',R*p==s.Matrix([qq(28,615),qq(-2,205)]))
subs={D:1,X:p[0],Y:p[1]}
ck('initial contact coordinates',(x0.subs(subs),y0.subs(subs))==(qq(217,615),qq(128,205)))
ck('physical triple equality',eq((qq(5,3)*(D-y1)-(D-x1)).subs(subs),0))
ck('contact x after A',x1.subs(subs)==qq(46,123))
for name,g,point in [('reject',(217,167,231),p),('accept',(233,171,211),R*p)]:
    co=Q*s.Matrix(g)
    ck(f'{name} integer example',co[0]==615 and s.Matrix(co[1:])/615==point)
ellr=s.expand(c1+c2+c3+2*D)
ck('rotation clock',eq(ellr,qq(32134,855)*D+qq(30512,1425)*X-qq(9942,475)*Y))
ell=s.expand(ellr+3*(xr+yr+D))
ck('contracted clock',eq(ell,qq(37264,855)*D+qq(36497,1425)*X-qq(10227,475)*Y))
row=s.Matrix([[ell.coeff(v) for v in (D,X,Y)]])
T=row*(s.eye(3)-N).inv()
ck('accumulation clock',T==s.Matrix([[qq(74528,855),qq(53102,3705),qq(-144302,3705)]]))
ck('clock identity',T-T*N==row)
ck('clock uncentering',T[0]-T[1]/3-2*T[2]/3==qq(1204366,11115))
ck('mod5 idempotent',((3*3-1)%5,(2*3)%5)==(3,1))

data=json.loads((ROOT/'science/construction/RULES.json').read_text())
rules=data['explicit_rules']; speeds={a['name']:F(a['speed']) for a in data['meta_signals']}
ck('169 unique meta labels',len(speeds)==len(data['meta_signals'])==169)
ck('exact eight speeds',set(speeds.values())==set(map(F,('-1','-1/3','-1/4','-1/9','0','1/11','2/17','1'))))
ck('inert JSON return',s.Matrix([[qq(e) for e in r] for r in data['gap_return_matrix']])==M)
ck('138 explicit rows',len(rules)==138)

# Static identities, roles and direction changes from L/H grammar. No positions,
# timestamps, trajectories, or input-dependent selection are calculated here.
expected=[]
def phase(name,target,anchor,reflector,inner,between,direction,velocity,kind):
    temp=f'{target}_{name}'
    ck(f'temporary speed {temp}',speeds[temp]==velocity)
    def ev(mark,role,sgn):
        mi=temp if role=='restore' else mark+'0'
        mo=temp if role=='launch' else mark+'0'
        flip=role=='bounce' or (kind=='L' and role in ('launch','restore'))
        expected.append((name,mi,mo,sgn,-sgn if flip else sgn))
        return -sgn if flip else sgn
    q=direction
    if kind=='L':
        for m in inner:q=ev(m,'pass',q)
        q=ev(target,'launch',q)
        for m in inner[::-1]:q=ev(m,'pass',q)
        q=ev(anchor,'bounce',q)
        for m in inner:q=ev(m,'pass',q)
        q=ev(target,'restore',q)
        for m in inner[::-1]:q=ev(m,'pass',q)
        q=ev(anchor,'bounce',q)
    else:
        q=ev(target,'launch',q)
        for m in between:q=ev(m,'pass',q)
        q=ev(reflector,'bounce',q)
        for m in between[::-1]:q=ev(m,'pass',q)
        q=ev(target,'restore',q)
        q=ev(anchor,'bounce',q)
    ck(f'direction restored {name}',q==direction)
for start,reflect in [(1,False),(9,True),(17,False)]:
    target,anchor,near,far,sgn=('Y','D','X','L',-1) if reflect else ('X','L','Y','D',1)
    va,vb=(F('-1/4'),F('2/17')) if reflect else (F('-1/9'),F('1/11'))
    for off in range(8):
        kind='L' if off%2==0 else 'H'; nearuse=off%4<2
        phase(f'{kind}{start+off:02}',target,anchor,near if nearuse else far,[],[] if nearuse else [near],sgn,va if nearuse else vb,kind)
    if start==1:
        expected.extend([('right','X0','X0',1,1),('right','Y0','Y0',1,1),('right','D0','D0',1,-1)])
    if start==9:
        expected.extend([('left','Y0','Y0',-1,-1),('left','X0','X0',-1,-1),('left','L0','L0',-1,1)])
for n,target,inside in [(25,'X',[]),(26,'Y',['X']),(27,'D',['X','Y'])]:
    phase(f'L{n}',target,'L',None,inside,[],1,F('-1/3'),'L')
ck('static grammar count',len(expected)==138)
printed=[l for l in (ROOT/'assets/rules.tex').read_text().splitlines() if re.match(r'^\d+ & ',l)]
ck('138 printed rules',len(printed)==138)
receipt=[]
for j,(r,e,pr) in enumerate(zip(rules,expected,printed)):
    ph,mi,mo,vi,vo=e
    ck(f'grammar rule {j}',(r['primitive'].removeprefix('transfer_'),r['marker_in'],r['marker_out'],F(r['messenger_in_speed']),F(r['messenger_out_speed']))==e)
    ck(f'input/output rule {j}',r['index']==j and r['input']==[f'Q{j}',mi] and r['output']==[f'Q{(j+1)%138}',mo])
    ck(f'physical speeds rule {j}',speeds[f'Q{j}']==vi and speeds[f'Q{(j+1)%138}']==vo and speeds[mi]!=vi and speeds[mo]!=vo)
    col=[x.strip() for x in pr.split('&')]
    ck(f'appendix rule {j}',int(col[0])==j and col[1]==ph and [label(x) for x in col[2:5]]==[mi,mo,f'Q{(j+1)%138}'] and rat_tex(col[5])==vi and rat_tex(col[6].split(r'\\')[0])==vo)
    receipt.append({'index':j,'phase':ph,'incoming_order':sorted(r['input'],key=lambda x:-speeds[x]),'outgoing_order':sorted(r['output'],key=lambda x:speeds[x])})
temporary=[l for l in (ROOT/'assets/rules.tex').read_text().splitlines() if l.startswith(r'\texttt{')]
ck('27 printed temporary labels',len(temporary)==27)
for line in temporary:
    a,b=line.split('&'); ck(f'appendix speed {label(a)}',rat_tex(b.split(r'\\')[0])==speeds[label(a)])
ck('variant closure speed',rules[113]['output'][0]=='Q114' and speeds['Q114']==speeds['Q0']==1 and rules[113]['marker_out']=='L0')
ck('final closure',rules[137]['output']==['Q0','L0'])

manuscript=(ROOT/'Report57.tex').read_text()
groups=[]
for j,e in enumerate(expected):
    phase_name=e[0]; identity=e[1][0]
    if not groups or groups[-1][0]!=phase_name:groups.append([phase_name,j,j,identity])
    else:groups[-1][2]=j;groups[-1][3]+=identity
phase_table=re.search(r'\\caption\{All finite phases.*?\\end\{longtable\}',manuscript,re.S)[0]
phase_lines=[l for l in phase_table.splitlines() if re.match(r'^(?:[LH]\d+|transfer )',l)]
ck('29 printed phases',len(phase_lines)==len(groups)==29)
for (name,start,end,word),line in zip(groups,phase_lines):
    fields=[v.strip() for v in line.split('&')]
    ck(f'printed complete phase {name}',fields[0].removeprefix('transfer ')==name and fields[1]==f'{start}--{end}' and fields[2].split(r'\\')[0]==word)
pinfiles=['science/construction/PROOF.md','science/construction/RULES.json','science/construction/GUARDS.txt','science/companion/BOUNDARY_AND_ARITHMETIC.md','independent_audit/INDEPENDENT_AUDIT.md','dependency_report56/PROOF.md','dependency_report56/AUDIT.md']
pins=re.findall(r'\\sha\{([a-f0-9]{64})\}',manuscript)
ck('all seven source pins',pins==[hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in pinfiles])

result={'verdict':'PASS','scope':'new exact endpoint/clock algebra and inert JSON/TeX binding, not simulation','check_count':len(checks),'checks':checks,'derived_guard_coefficients':[[str(f.coeff(v)) for v in (D,X,Y)] for f in guards],'distances_squared':[str(d) for d in dist],'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'Report57.tex',ROOT/'assets/guards.tex',ROOT/'assets/rules.tex',ROOT/'science/construction/RULES.json',ROOT/'science/construction/GUARDS.txt']}}
(OUT/'new_algebra_and_binding_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'new_all_138_local_orders.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','check_count':len(checks),'guard_count':len(guards),'explicit_rule_count':len(rules)}))
