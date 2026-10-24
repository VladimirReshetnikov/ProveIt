"""Authored exact symbolic construction, independent of upstream programs."""
import json,pathlib,collections,hashlib
R=pathlib.Path(__file__).resolve().parent
def require(v,msg):
 if not v:raise ValueError(msg)
def construct(source,weights,targets,signs):
 n=len(weights); W=max(weights); layers=[{}for _ in range(3)]
 for j,row in enumerate(source['equations']):
  grouped={}
  for t in row['terms']:
   a=tuple(t['powers'][:n]);p=tuple(t['powers'][n:]);grouped.setdefault(a,collections.defaultdict(int))[p]+=t['coefficient']
  for a,coeff in grouped.items():
   d=sum(a); e=targets[j]-sum(x*y for x,y in zip(a,weights));mult=1 if d==2 and max(a)==1 else 2
   c=tuple(sorted((p,v*mult*signs[j])for p,v in coeff.items()if v))
   require(e>=0,'negative kernel exponent')
   require(e not in layers[d]or layers[d][e]==c,'incompatible shared tap')
   layers[d][e]=c
 mon=[[((),0,1)],[( (i,),weights[i],1)for i in range(n)],[( (i,j),weights[i]+weights[j],1 if i==j else 2)for i in range(n)for j in range(i,n)]]
 actual=[collections.defaultdict(int)for _ in targets];ti={q:j for j,q in enumerate(targets)};count=0
 require(len(ti)==len(targets),'duplicate target')
 for d,layer in enumerate(layers):
  for e,c in layer.items():
   for inds,v,m in mon[d]:
    count+=1
    if e+v not in ti:continue
    a=[0]*n
    for i in inds:a[i]+=1
    for p,z in c:actual[ti[e+v]][tuple(a)+p]+=z*m
 for j,row in enumerate(source['equations']):
  want={tuple(t['powers']):2*signs[j]*t['coefficient']for t in row['terms']};got={p:v for p,v in actual[j].items()if v}
  require(got==want,'full symbolic target identity '+str(j+1))
 deg=[max(x)for x in layers];H=max(deg[d]+d*W for d in range(3));lead=[layers[d][deg[d]]for d in range(3)]
 require(all(v>0 for p,v in lead[2]),'quadratic positive leading coefficient')
 require(H-max(targets)>=2,'target headroom')
 return {'weights':weights,'targets_by_row':targets,'targets':sorted(targets),'row_orientations':signs,'max_weight':W,'convolution_height':H,'maximum_target':max(targets),'kernel_degrees':deg,'kernel_positions':sum(map(len,layers)),'leading_coefficients':lead,'dominance_gaps':[H-deg[d]-d*W for d in range(3)],'exhaustive_interactions':count}, {'variables':source['variables'],'ports':source['constants'],'formula':'G(B,U)=D2(B)*U^2+D1(B)*U+D0(B)','kernels':[{'degree':d,'terms':[{'exponent':e,'coefficient':[{'powers':list(p),'coefficient':v}for p,v in c]}for e,c in sorted(x.items())]}for d,x in enumerate(layers)]}
def main():
 source=json.loads((R/'source.json').read_text()); layout=json.loads((R/'layout.json').read_text());kernel=json.loads((R/'kernels.json').read_text())
 code,got=construct(source,layout['weights'],layout['targets_by_row'],layout['row_orientations'])
 require(json.loads(json.dumps(code))==layout,'layout exact reconstruction');require(got==kernel,'kernel exact reconstruction')
 old=json.loads((R/'prior_kernels.json').read_text())
 def coeffs(k):return collections.Counter((l['degree'],tuple(sorted((tuple(c['powers']),c['coefficient'])for c in t['coefficient'])))for l in k['kernels']for t in l['terms'])
 require(coeffs(old)==coeffs(kernel),'exact inherited coefficient multiset')
 # Corruption controls authenticate rejection of algebraically invalid layouts.
 q=layout['targets_by_row'][:];q[0]=q[1]
 try:construct(source,layout['weights'],q,layout['row_orientations'])
 except ValueError:pass
 else:raise ValueError('duplicate target negative control')
 print(json.dumps({'status':'PASS','identities':22,'interactions':code['exhaustive_interactions'],'height':code['convolution_height'],'coefficient_multiset':'exact inherited equality','negative_controls':1}))
if __name__=='__main__':main()
