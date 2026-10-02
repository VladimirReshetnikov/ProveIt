import pathlib,json,math
p=pathlib.Path(__file__).parent
exec((p/'check_renewal.py').read_text().split('rows=[]')[0])
rows=[]
for m in [10,20,40]:
 for rho in [.5,.75,1.5,2.]:
  k=round(m*rho);r=k/m;P=success(m,k);T=float(P if r>1 else 1-P)
  I=1-r+r*math.log(r);leading=math.exp(1-1/r)*math.sqrt(r)/(abs(r-1)*math.sqrt(2*math.pi*m))*math.exp(-m*I)
  c1=-(r**4+10*r**3-17*r*r+24*r-6)/(12*r**3*(r-1)**2)
  rows.append({'m':m,'k':k,'rho':r,'tail':T,'leading':leading,'ratio':T/leading,'c1':c1,'first_ratio':T/(leading*(1+c1/m)),'scaled_first_error':m*m*(T/leading-1-c1/m)})
print(json.dumps(rows,indent=2));(p.parent/'checks'/'rare-tail-exact-checks.json').write_text(json.dumps(rows,indent=2))
