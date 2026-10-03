from cover3 import *
import sympy as s
classes={}
for core,signs,types in templates():
 g=support_polys(core,signs,types)
 if not g[3]:continue
 keys=[]
 for p in permutations(range(3)):
  for rev in (False,True):
   es=tuple(sorted((p[j],p[i])if rev else(p[i],p[j])for i,j in core if i!=j))
   ss=[0]*3
   for i in range(3):ss[p[i]]=(-1 if rev else 1)*signs[i]
   ty=tuple(sorted(sum(1<<p[i]for i in range(3)if mask>>i&1)for mask in types))
   keys.append((es,tuple(ss),ty))
 key=min(keys);classes[key]=classes.get(key,0)+1
out=[]
for idx,((es,signs,types),mult)in enumerate(classes.items()):
 core=set(es)|{(i,i)for i in range(3)};g=support_polys(core,signs,types)
 xs=s.symbols(' '.join('n'+str(t)for t in types),seq=True)
 def mono(poly):return s.expand(sum(v*s.prod(s.prod(x-j for j in range(r))/s.factorial(r)for x,r in zip(xs,q))for q,v in poly.items()))
 D=gap(g[1],g[2],g[3],3)
 out.append({'id':idx,'core_arcs':es,'signs':signs,'types':types,'labeled_multiplicity':mult,'gamma_monomial':[str(mono(a))for a in g],'gap_monomial':str(mono(D)),'gamma_binomial':[[[list(q),v]for q,v in a.items()]for a in g],'gap_binomial':[[list(q),v]for q,v in D.items()],'binomial_coefficientwise_positive':all(v>=0 for v in D.values())})
Path(__file__).with_name('cover3_seventeen_templates.json').write_text(json.dumps(out,indent=2)+'\n')
print('17 classes; coefficientwise positives',[r['id']for r in out if r['binomial_coefficientwise_positive']])
