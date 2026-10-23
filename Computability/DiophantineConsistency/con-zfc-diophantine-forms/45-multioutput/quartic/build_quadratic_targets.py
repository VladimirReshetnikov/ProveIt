"""Generate exact shifted residual coefficients, not an SOS."""
import json,pathlib,sympy as s,math,hashlib
ROOT=pathlib.Path(__file__).resolve().parent
src=ROOT.parent/'review/sources/31-sun10/quartic31/quartic31_system60.json';d=json.loads(src.read_text());vs=s.symbols(' '.join(d['variables']));e=dict(zip(d['variables'],vs));e.update({x:s.Symbol(x) for x in d['constants']})
def g(x):return x if isinstance(x,int) else e[x]
for name,op,a,b in d['source']:
 a,b=g(a),g(b);e[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
polys=[s.Poly((g(a)-g(b)).subs({v:v+1 for v in vs},simultaneous=True),*vs) for a,b in d['comparisons']]
b2=json.loads((ROOT/'B2_CERTIFICATE.json').read_text());w=b2['weights'];W=max(w);spacing=2*W+1
order=[j for j in range(22) if j!=4]+[4]
rows=[]
for pos,j in enumerate(order,1):
 P=polys[j];assert P.total_degree()==2
 target=pos*spacing
 terms=[]
 for alpha,coef in P.terms():
  weight=sum(a*b for a,b in zip(alpha,w));factor=math.factorial(2-sum(alpha))*math.prod(math.factorial(a) for a in alpha)
  terms.append({'alpha':list(alpha),'coefficient':str(s.expand(coef)),'multinomial_inverse_weight':factor,'weighted_coefficient':str(s.expand(factor*coef)),'weight':weight,'encoding_exponent':target-weight})
 rows.append({'original_row_one_based':j+1,'target_exponent':target,'constant_coefficient':str(P.coeff_monomial(1)),'terms':terms})
assert rows[-1]['constant_coefficient']=='1'
out={'source_pin':'22e75dd6b87b1b199bb08c778d7cf075ae5aae08','source_file':'../review/sources/31-sun10/quartic31/quartic31_system60.json','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'variables':d['variables'],'ports':d['constants'],'domain':'nonnegative integer coordinates n; every original positive variable is n+1','weights':w,'maximum_weight':W,'target_spacing':spacing,'row_order_one_based':[j+1 for j in order],'row_count':22,'target_maximum':22*spacing,'shifted_row_term_count':sum(len(r['terms']) for r in rows),'leading_encoded_coefficient':2,'rows':rows}
(ROOT/'QUADRATIC_TARGETS.json').write_text(json.dumps(out,indent=2)+'\n'); print({k:out[k] for k in ['maximum_weight','target_spacing','row_count','target_maximum','shifted_row_term_count','leading_encoded_coefficient']})
