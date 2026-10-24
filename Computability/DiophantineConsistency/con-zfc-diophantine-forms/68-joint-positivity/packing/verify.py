"""Independent exact target reconstruction; never executes imported programs."""
import json,collections,pathlib,hashlib
R=pathlib.Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def build(name):
 inp=json.loads((R/(name+'_input.json')).read_text());s=inp['source'];w=inp['weights'];W=max(w);n=len(w)
 line=(R/(name+'.log')).read_text().splitlines()[-1];parts=list(map(int,line.split()));q=parts[1:];require=len(q)==22
 if not require:raise ValueError('target count')
 taps=[{}for _ in range(3)]
 for j,row in enumerate(inp['rows']):
  for rec in row:
   d=rec['d'];e=q[j]-rec['p'];c=tuple((tuple(a),v)for a,v in rec['c'])
   if e<0:raise ValueError('negative exponent')
   if e in taps[d] and taps[d][e]!=c:raise ValueError('incompatible overlap')
   taps[d][e]=c
 cand=[[((),0,1)],[],[]]
 for i in range(n):cand[1].append(((i,),w[i],1))
 for i in range(n):
  for j in range(i,n):cand[2].append(((i,j),w[i]+w[j],1 if i==j else 2))
 extracted=[collections.defaultdict(int)for _ in q];targ={v:j for j,v in enumerate(q)};interactions=0;hits=0
 for d,layer in enumerate(taps):
  for e,c in layer.items():
   for inds,v,mult in cand[d]:
    interactions+=1
    if e+v not in targ:continue
    hits+=1;a=[0]*n
    for i in inds:a[i]+=1
    for p,cc in c:extracted[targ[e+v]][tuple(a)+p]+=cc*mult
 for j,row in enumerate(s['equations']):
  want={tuple(t['powers']):2*t['coefficient']for t in row['terms']};got={a:c for a,c in extracted[j].items()if c}
  if got!=want:raise ValueError(('identity mismatch',name,j,got,want))
 degrees=[max(layer)for layer in taps];H=max(degrees[d]+d*W for d in range(3))
 leading=[[[list(a),v]for a,v in layer[max(layer)]]for layer in taps]
 positive=[all(v>0 for a,v in layer[max(layer)])for layer in taps]
 gaps=[H-(degrees[d]+d*W)for d in range(3)]
 if not positive[2] or not all(positive[d] or gaps[d]>=1 for d in range(2)):raise ValueError('positivity')
 if H-max(q)<2:raise ValueError('target margin')
 kern={'variables':s['variables'],'ports':['beta','K0','MC','MF'],'source_sha256':digest(R/(name+'_source.json')),'formula':'G(B,U)=D2(B)*U^2+D1(B)*U+D0(B)','kernels':[{'degree':d,'terms':[{'exponent':e,'coefficient':[{'powers':list(a),'coefficient':v}for a,v in c]}for e,c in sorted(layer.items())]}for d,layer in enumerate(taps)]}
 code={'name':name+'_shared','weights':w,'targets_by_row':q,'targets':sorted(q),'order':[j+1 for j in sorted(range(22),key=q.__getitem__)],'max_weight':W,'convolution_height':H,'maximum_target':max(q),'kernel_degrees':degrees,'row_orientations':[1]*22,'records':sum(map(len,inp['rows'])),'kernel_positions':sum(map(len,taps)),'source_sha256':digest(R/(name+'_source.json')),'leading_coefficients':leading,'positive_leading_coefficients':positive,'dominance_gaps':gaps,'exhaustive_interactions':interactions,'target_hits':hits}
 (R/(name+'_kernels.json')).write_text(json.dumps(kern,indent=2)+'\n');(R/(name+'_code.json')).write_text(json.dumps(code,indent=2)+'\n')
 return {'name':name,'height':H,'positions':code['kernel_positions'],'records':code['records'],'degrees':degrees,'leading':leading,'identities':22,'interactions':interactions,'status':'PASS'}
def main():
 result=[]
 for name in ['gapN86','gapNq85','gapL86','gap87','split89']:
  inp=json.loads((R/(name+'_input.json')).read_text());(R/(name+'_source.json')).write_text(json.dumps(inp['source'],indent=2)+'\n');result.append(build(name))
 (R/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
