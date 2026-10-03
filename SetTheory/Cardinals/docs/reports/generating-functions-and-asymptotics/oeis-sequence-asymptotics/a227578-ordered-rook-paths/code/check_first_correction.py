import sympy as s,json
k=s.symbols('k',positive=True,integer=True)
mu=(k+1)/k**2;a=(k+1)*(k+2)/k**3;b=(k+1)*(k*k+6*k+6)/k**4;c=(k+1)*(k**3+14*k*k+36*k+24)/k**5;v=a/mu
A2=(k-1)*a/(2*k*mu)-(k-1)*mu/2-k/12-a*a/(2*k*mu*mu)+b/(2*k*mu)
B2=a**3/(8*k*mu**3)-a*b/(4*k*mu**2)
P2=(k*k-1)/v;P22=(k*k-1)*(k*k+1)/v**2;P4=(k*k-1)*(2*k*k-3)/(k*v**2);P32=3*(k*k-1)*(k*k-4)/(k*v**3)
d1=s.factor(A2*P2+B2*P22+c*P4/(24*mu)-b*b*P32/(72*mu*mu))
target=-(k-1)*(k+1)*(2*k**4+8*k**3+9*k*k+6*k+12)/(12*k*(k+2)**2)
assert s.factor(d1-target)==0
print(d1)
json.dump(dict(d1=str(d1),values={str(j):str(d1.subs(k,j)) for j in range(2,9)},status='Symbolic algebra verified from independently checked Gaussian moments; k3 independently verified from exact rational residue'),open('first-correction-check.json','w'),indent=2)
