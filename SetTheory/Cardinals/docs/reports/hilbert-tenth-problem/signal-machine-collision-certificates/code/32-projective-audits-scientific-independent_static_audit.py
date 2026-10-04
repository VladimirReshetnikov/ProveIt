#!/usr/bin/env python3
"""Independent symbolic audit; never runs a machine, source checker, or schedule.

Inputs are frozen JSON declarations, authenticated as inert bytes. Symbolic
identities below are reconstructed from the proof's equations. Rule comparison
is syntactic: it neither advances positions nor determines a next collision.
Writes are restricted to this separate audit's evidence directory.
"""
from pathlib import Path
from hashlib import sha256
import json
import stat
import sympy as S

SOURCE = Path('/workspace/shared/projective-signal-shears62-20261004')
HERE = Path(__file__).resolve().parent
OUT = HERE / 'evidence'
EXPECTED_PROOF = '502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47'
assert sha256((SOURCE/'PROOF.md').read_bytes()).hexdigest() == EXPECTED_PROOF
checks = []
def equal(name, lhs, rhs):
    residual = lhs-rhs
    entries = list(residual) if isinstance(residual, S.MatrixBase) else [residual]
    assert all(S.cancel(e) == 0 for e in entries), name
    checks.append(name)
def truth(name, proposition):
    assert proposition, name
    checks.append(name)

v,D,x,y,a,b,q,c,t = S.symbols('v D x y a b q c t')
R = S.Rational
h = (v-1)/(v+1)
s = (v+2)/3
d = y+v*(D-y)
# Independently solve the two affine lines, using the anchor-bounce time.
bounce = 2*D-y
meeting = S.cancel((y-bounce-D+h*D)/(h-1))
equal('outer restore meeting time', meeting, (v+2)*D-(v+1)*y)
equal('outer restore location', D+h*(meeting-D), d)
times = [0,x,y,D,bounce,meeting,meeting+d-y,meeting+d-x,meeting+d]
positions = [0,x,y,D,y,d,y,x,0]
flights = [x,y-x,D-y,D-y,v*(D-y),v*(D-y),y-x,x]
velocities = [1,1,1,-1,1,-1,-1,-1]
for i in range(8):
    equal(f'outer flight {i+1}',times[i+1]-times[i],flights[i])
    equal(f'outer messenger segment {i+1}',positions[i+1]-positions[i],velocities[i]*flights[i])
equal('outer gap at bounce',D+h*(bounce-D)-y,2*v*(D-y)/(v+1))
equal('outer duration',times[-1],2*(D+v*(D-y)))
equal('raw guard',d-s*y,v*D+(1-4*v)*y/3)
equal('raw center margin',(d-s*y).subs(y,2*D/3),(v+2)*D/9)
# Primitive endpoints and all spectator-time interleavings use only q>0,a>0,
# and 0<p<min(q,a*q); the review gives the inequality proof.
alpha,Q,p = S.symbols('alpha Q p')
velocity = (alpha-1)/(alpha+1)
equal('anchor-scale moving target endpoint',Q+velocity*((2+alpha)*Q-Q),alpha*Q)
principal = [0,Q,2*Q,(2+alpha)*Q,(2+2*alpha)*Q]
spectator = [p,2*Q-p,2*Q+p,2*(1+alpha)*Q-p]
equal('anchor-scale duration',principal[-1],2*(1+alpha)*Q)

physical = S.Matrix([[v,0,1-v],[0,s,0],[0,0,s]])
center_to_physical = S.Matrix([[1,0,0],[R(1,3),1,0],[R(2,3),0,1]])
N = S.Matrix([[s,0,1-v],[0,s,(v-1)/3],[0,0,v]])
equal('raw centered conjugacy',center_to_physical.inv()*physical*center_to_physical,N)
equal('raw determinant',N.det(),v*s*s)
Av = N[1:3,1:3]
Cv = s*Av.inv()
equal('compensator shape',Cv,S.Matrix([[1,(1-v)/(3*v)],[0,s/v]]))
compensator = S.diag(1/s,1,1)
compensator[1:3,1:3] = Av.inv()
k = 3*(1-v)/(v+2)
Ek = S.Matrix([[1,0,k],[0,1,0],[0,0,1]])
equal('compensated scale shear',compensator*N,Ek)
equal('inverse parameter',((3-2*q)/(3+q)).subs(q,k),v)
equal('coefficient lower range margin',k+3,9/(v+2))
equal('coefficient upper range margin',R(3,2)-k,9*v/(2*(v+2)))
equal('coefficient derivative',S.diff(k,v),-9/(v+2)**2)
B = S.Matrix([[b,-a],[a,b]])
equal('conjugator determinant',B.det(),a*a+b*b)
DB = S.diag(1,1,1); DB[1:3,1:3] = B
Eone = S.Matrix([[1,0,1],[0,1,0],[0,0,1]])
equal('arbitrary scale row conjugation',DB.inv()*Eone*DB,S.Matrix([[1,a,b],[0,1,0],[0,0,1]]))
s0,b1,b2,A11,A12,A21,A22=S.symbols('s0 b1 b2 A11 A12 A21 A22')
Erow=S.Matrix([[1,b1/s0,b2/s0],[0,1,0],[0,0,1]])
F=S.Matrix([[s0,0,0],[0,A11,A12],[0,A21,A22]])
equal('final full requested lift',F*Erow,S.Matrix([[s0,b1,b2],[0,A11,A12],[0,A21,A22]]))
# The count fixture is reconstructed using the dependency's explicit formulas.
U=lambda z:S.Matrix([[1,z],[0,1]])
V=lambda z:S.Matrix([[1,0],[z,1]])
C1=S.Matrix([[1,1],[0,3]])
B1=S.diag(R(1,3),1)*C1
equal('coefficient-one SL2 factors',V(6)*U(R(1,3))*V(-2),B1)
subdivisions=[int(S.ceiling(4*abs(z))) for z in [-2,R(1,3),6]]
truth('coefficient-one shear subdivision list',subdivisions==[8,2,24])
K=sum(subdivisions); T=4; H=int(S.ceiling(R(4*abs(3-1),min(1,3)))); blocks=3
counts={'events':20+18*K+3*T+14*H+24,'temporary_marker_labels':3+4*K+3*H+3,'guards':4+4*K+4*blocks+8*H}
counts['meta_signals']=counts['events']+counts['temporary_marker_labels']+4
truth('coefficient-one exact count',counts=={'events':780,'temporary_marker_labels':166,'guards':216,'meta_signals':950})

r=s/v; loss=(v-1)/v
M44=S.Matrix([[1,0,-loss],[0,r,0],[0,0,r]])
invariant=S.Matrix([[1,0,-R(3,2)]])
equal('44 return from global homothety',physical/v,M44)
equal('44 invariant covector',invariant*M44,invariant)
equal('44 contraction gap',1-r,2*loss/3)
closed=S.Matrix([c+R(3,2)*y*t,x*t,y*t])
closednext=S.Matrix([c+R(3,2)*y*t*r,x*t*r,y*t*r])
equal('44 closed form recurrence',M44*closed,closednext)
equal('44 nth next gap',closednext[0]-closednext[2],c+y*t*r/2)
equal('44 exact raw guard/output gap',(d-s*y)/v,(M44*S.Matrix([D,x,y]))[0]-(M44*S.Matrix([D,x,y]))[2])
Traw=2*(D+v*(D-y))+2*(1+s)*(x+y)
T44=Traw+2*(1+1/v)*(s*x+s*y+d)
equal('44 clock D coefficient',S.diff(T44,D),4*(v+1))
equal('44 clock x coefficient',S.diff(T44,x),2+4*s+2*s/v)
equal('44 clock y coefficient',S.diff(T44,y),2+4*s+2*s/v+2/v-4*v)
equal('44 center ray eigenvalue',M44*S.Matrix([1,R(1,3),R(2,3)]),r*S.Matrix([1,R(1,3),R(2,3)]))
equal('44 characteristic polynomial',M44.charpoly(q).as_expr(),(q-1)*(q-r)**2)
# Native positive-integer input certificates: coefficient identities only.
g1,g2,g3,w=S.symbols('g1 g2 g3 w'); L=2*g3-g1-g2
polys=[(L-w+1)**2,L**2,(L-w)**2]
truth('native degree-two certificates',all(S.Poly(P,g1,g2,g3,w).total_degree()==2 for P in polys))
equal('native invariant in original gaps',(D-R(3,2)*y).subs({D:g1+g2+g3,y:g1+g2}),L/2)
equal('unique infinite witness substitution',polys[0].subs(w,L+1),0)
equal('unique non-Zeno witness substitution',polys[2].subs(w,L),0)
# This uncovered GL3 map is checked independently, not treated as impossible.
Pg=S.Matrix([[1,1,1],[1,2,1],[1,1,3]])
equal('uncovered positive gap determinant',Pg.det(),2)
equal('uncovered positive gap cubic',Pg.charpoly(q).as_expr(),q**3-6*q*q+8*q-2)
truth('uncovered cubic has no rational root',all(Pg.charpoly(q).as_expr().subs(q,z)!=0 for z in [1,-1,2,-2]))
gap_from_center=S.Matrix([[R(1,3),1,0],[R(1,3),-1,1],[R(1,3),0,-1]])
equal('uncovered positive gap centered conjugacy',gap_from_center.inv()*Pg*gap_from_center,S.Matrix([[4,-1,-1],[-R(1,3),R(1,3),R(1,3)],[-R(1,3),-R(1,3),R(5,3)]]))

# Independent static comparison of all 44 rules, with no physical replay.
rules_data=json.loads((SOURCE/'RULES44.json').read_text())
rules=rules_data['rules']; speed=rules_data['meta_signal_speeds']
outer=[('X','X',1),('Y','Y',1),('R','R_outer',-1),('Y','Y',1),('R_outer','R',-1),('Y','Y',-1),('X','X',-1),('L','L',1)]
innerY=[('X','X',1),('Y','Y_inner',-1),('X','X',-1),('L','L',1),('X','X',1),('Y_inner','Y',-1),('X','X',-1),('L','L',1)]
innerX=[('X','X_inner',-1),('L','L',1),('X_inner','X',-1),('L','L',1)]
globalX=[('X','X_global',-1),('L','L',1),('X_global','X',-1),('L','L',1)]
globalY=[('X','X',1),('Y','Y_global',-1),('X','X',-1),('L','L',1),('X','X',1),('Y_global','Y',-1),('X','X',-1),('L','L',1)]
globalR=[('X','X',1),('Y','Y',1),('R','R_global',-1),('Y','Y',-1),('X','X',-1),('L','L',1),('X','X',1),('Y','Y',1),('R_global','R',-1),('Y','Y',-1),('X','X',-1),('L','L',1)]
expected=outer+innerY+innerX+globalX+globalY+globalR
truth('44 complete rule count',len(rules)==len(expected)==44)
truth('44 meta-signal count',len(speed)==54)
truth('44 input sets unique',len({tuple(sorted(R['input'])) for R in rules})==44)
rule_rows=[]
for i,((zin,zout,vout),rule) in enumerate(zip(expected,rules)):
    nxt=(i+1)%44
    truth(f'rule {i+1} complete literal pair',rule=={'event':i+1,'input':[f'Q{i}',zin],'output':[f'Q{nxt}',zout]})
    truth(f'rule {i+1} outgoing Q speed',speed[f'Q{nxt}']==str(vout))
    rule_rows.append({'event':i+1,'marker_input':zin,'marker_output':zout,'messenger_in_speed':speed[f'Q{i}'],'messenger_out_speed':str(vout)})
truth('44 stationary role speeds',all(speed[z]=='0' for z in ['L','X','Y','R']))
truth('44 temporary speed tags',{z:speed[z] for z in ['R_outer','Y_inner','X_inner','X_global','Y_global','R_global']}=={'R_outer':'h','Y_inner':'p','X_inner':'p','X_global':'-h','Y_global':'-h','R_global':'-h'})
equal('44 inner speed agrees with scale s',(s-1)/(s+1),(v-1)/(v+5))
equal('44 global speed agrees with scale 1/v',(1/v-1)/(1/v+1),-h)
truth('44 declared speed definitions',rules_data['speed_parameters']=={'h':'(v-1)/(v+1)','p':'(v-1)/(v+5)'})
truth('44 number-preserving binary rules',all(len(R['input'])==len(R['output'])==2 and len(set(R['input']))==len(set(R['output']))==2 for R in rules))
truth('44 every temporary label launched/restored once',all(sum(z in R['output'] for R in rules)==sum(z in R['input'] for R in rules)==1 for z in ['R_outer','Y_inner','X_inner','X_global','Y_global','R_global']))

# Authenticate all existing source files and preserve frozen bytes/modes/mtimes.
manifest=json.loads((SOURCE/'MANIFEST.json').read_text())
truth('all manifest file hashes',all(sha256((SOURCE/entry['path']).read_bytes()).hexdigest()==entry['sha256'] and (SOURCE/entry['path']).stat().st_size==entry['bytes'] for entry in manifest['files']))
before=json.loads((OUT/'frozen_before.json').read_text())
after=[]
for path in [SOURCE]+sorted(SOURCE.rglob('*')):
    st=path.lstat()
    row={'path':'.' if path==SOURCE else str(path.relative_to(SOURCE)),'mode':oct(stat.S_IMODE(st.st_mode)),'mtime_ns':st.st_mtime_ns,'size':st.st_size,'kind':'file' if path.is_file() else 'directory'}
    if path.is_file():row['sha256']=sha256(path.read_bytes()).hexdigest()
    after.append(row)
truth('frozen bytes modes mtimes preserved',before==after)
(OUT/'frozen_after.json').write_text(json.dumps(after,indent=2)+'\n')
(OUT/'rule44_static_review.json').write_text(json.dumps(rule_rows,indent=2)+'\n')
result={'status':'PASS','scope':'Independent symbolic identities and static declaration comparison only; no author checker, constructor, physical simulator or saved schedule executed.','proof_sha256':EXPECTED_PROOF,'audit_source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'sympy_version':S.__version__,'check_count':len(checks),'checks':checks,'coefficient_one_counts':counts,'mixed_clock_duration':str(S.factor(T44)),'preserved_source_objects':len(after)}
(OUT/'independent_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key] for key in ['status','check_count','proof_sha256','audit_source_sha256','sympy_version','coefficient_one_counts','preserved_source_objects']},indent=2))
