"""Compare every printed compact residual with the literal polynomial artifact."""
import pathlib,json,sympy as s
p=pathlib.Path(__file__).resolve().parent
d=json.loads((p/'guards/signed34_sextic.json').read_text())
z={n:s.Symbol(n) for n in d['variables']+d['fixed_numerals']}
globals().update(z)
q=beta*J+1;k=eta+zeta;H=4*a+3;C=q-F-alpha;X=D-a*c-H*gamma
R=((q-1)*(q-F)+alpha)*L+J*(MC+q*MF)
def pos(prefix):
 x,y,z1=[z[prefix+str(i)] for i in (1,2,3)]
 return x*x+y*y+z1*z1+z1+1
rs=[L-q*q+1,a-E-(2*v_scale+1)*q*(L+1),E*(X+1)-a*X,c-k*(a-E)-eta,tau*tau+(2*tau-k)*E*(c-eta)-1,Delta-a*a-4*a-3,D*D-Delta*c*c-1,k-1-E*h-R,(K0*q+X)*C-q*F-Z*(q-1),V+c-f*o,V-c*j+k-1-E*h,I-(2*r+1)*c*c,Baux-I*I,Baux-Delta*f*f+Delta,Baux*V*V-Baux*y*y+y*y-1,X-4*q*u*u,F*alpha-pos('FA_pos'),F*C-pos('FC_pos'),eta*zeta-pos('eta_zeta_pos')]
for i,(actual,want) in enumerate(zip(d['residuals'],rs),1):
 if s.expand(s.sympify(actual,locals=z)-want)!=0:raise RuntimeError(f'Printed residual {i} disagrees')
if len(rs)!=19 or len(d['variables'])!=34:raise RuntimeError('dimensions')
print('PASS: all 19 displayed residuals equal literal JSON; 34 integer unknowns')
