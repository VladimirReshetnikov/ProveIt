"""Own exact symbolic algebra only: affine gadget endpoints and matrix identities.
No trajectory simulator, next-collision search, upstream code, or saved schedule.
"""
import sympy as s
X,Y,D=s.symbols('X Y D')
x=X+D/3
y=Y+2*D/3
rows=[]
def add(g,label):
    rows.append((s.expand(g),label))
def upper(x,y,label):
    vals=[x,x-y/4,x-y/4+D/6,x-y/2+D/6,x-y/2+D/3]
    add(y,label+' other > 0');add(D-y,label+' other < D')
    for i,z in enumerate(vals):
        add(z,f'{label} endpoint {i} > 0')
        add(y-z,f'{label} endpoint {i} < other')
    return s.expand(vals[-1])
x=upper(x,y,'A')
r,other=D-y,D-x
vals=[r,r+2*other/5,r+2*other/5-4*D/15,r+4*other/5-4*D/15,r+4*other/5-8*D/15]
add(other,'B other > 0');add(D-other,'B other < D')
for i,z in enumerate(vals):
    add(z,f'B endpoint {i} > 0');add(other-z,f'B endpoint {i} < other')
y=s.expand(D-vals[-1])
x=upper(x,y,'C')
print('Final x:',x)
print('Final y:',y)
expected_x=D/3+s.Rational(3,5)*X-s.Rational(4,5)*Y
expected_y=2*D/3+s.Rational(4,5)*X+s.Rational(3,5)*Y
assert s.expand(x-expected_x)==0 and s.expand(y-expected_y)==0
bounds=[]
for g,label in rows:
    a,b,c=g.coeff(X),g.coeff(Y),g.coeff(D)
    assert c>0,(label,c)
    if a*a+b*b:
        bounds.append((s.factor(c*c/(a*a+b*b)),label,g))
minimum=min(z[0] for z in bounds)
print('Squared inradius:',minimum)
print('Nearest guard(s):')
for value,label,g in bounds:
    if value==minimum:
        a,b,c=g.coeff(X),g.coeff(Y),g.coeff(D)
        contact=(s.factor(-c*a/(a*a+b*b)),s.factor(-c*b/(a*a+b*b)))
        print(label,':',g,'; contact (X,Y)=',contact)
R=s.Matrix([[s.Rational(3,5),-s.Rational(4,5)],[s.Rational(4,5),s.Rational(3,5)]])
A=s.Matrix([[1,-s.Rational(1,2)],[0,1]])
B=s.Matrix([[1,0],[s.Rational(4,5),1]])
assert A*B*A==R and R.T*R==s.eye(2)
M=s.Matrix([[7,-2,10],[14,11,-10],[-6,6,15]])/15
print('Gap return M:',M)
print('Characteristic polynomial:',s.factor(M.charpoly().as_expr()))
print('Number of guard rows:',len(rows))
with open('/workspace/shared/signal-map-obstruction-20261004/GUARDS.txt','w') as f:
    f.write('Centered coordinates X=x-D/3, Y=y-2D/3. Require every row > 0.\n')
    for g,label in rows:f.write(f'{label}: {g}\n')
