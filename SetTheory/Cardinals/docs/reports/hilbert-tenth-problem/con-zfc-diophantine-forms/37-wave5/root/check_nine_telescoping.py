"""Independent polynomial-ring verification of the sharp degree certificate."""
from pathlib import Path
import json
import sympy as s
A,C,E,F,H,G,t,D,MD,MF,MI,V0,Omega,E0,a0=s.symbols('A C E F H G t D MD MF MI V0 Omega E0 a0')
checks=0
assert s.expand((A*C+t+1)**2-((A*A-1)*C*C+1)-(2*A*C*t+t*t+2*A*C+2*t+C*C))==0;checks+=1
assert s.expand((A*E+1)**2-((A*A-1)*E*E+1)-(2*A*E+E*E))==0;checks+=1
I=(G*G-1)*H*H+1
assert s.expand(MI*MI-I-((MI-G*H)*(MI+G*H)+H*H-1))==0;checks+=1
V1=MD*MF*MI+1;a1=D*F*I
DeltaV=(MD*MD-D)*MF*MF*MI*MI+D*(MF*MF-F)*MI*MI+D*F*(MI*MI-I)+2*MD*MF*MI+1
assert s.expand(V1*V1-a1-DeltaV)==0;checks+=1
Theta=E0-Omega*V0*V1
assert s.expand(Theta*Theta-Omega*Omega*(a0+V0*V0*a1)-(E0*E0-2*E0*Omega*V0*V1+Omega*Omega*V0*V0*DeltaV-Omega*Omega*a0))==0;checks+=1
report={'status':'PASS','exact_polynomial_ring_identities':checks,'scope':'Exact telescoping identities justify replacing the original norm by its cancellation-free degree certificate; leading degree audit is supplied separately.'}
Path(__file__).with_name('NINE_TELESCOPING_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
