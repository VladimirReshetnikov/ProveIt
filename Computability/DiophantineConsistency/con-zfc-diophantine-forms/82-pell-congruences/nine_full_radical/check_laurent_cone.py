from pathlib import Path
import math,json,collections
R=Path(__file__).resolve().parent
def shift(p,idx,v):
 out=collections.defaultdict(int)
 for m,c in p.items():
  for k in range(m[idx]+1):
   n=list(m);n[idx]=k;out[tuple(n)]+=c*math.comb(m[idx],k)*v**(m[idx]-k)
 return {m:c for m,c in out.items()if c}
def report(p):
 neg={m:c for m,c in p.items()if c<0};return {'terms':len(p),'negative':len(neg),'negative_max_A':max((m[0]for m in neg),default=-1),'negative_example':list(neg.items())[:3]}
def main():
 x=json.loads((R/'laurent_candidate.json').read_text());cert={}
 for key in ['majorant','defect']:
  p={tuple(m):int(c)for m,c in x[key]}
  for idx,v in [(1,1),(2,1),(3,3),(0,3)]:
   p=shift(p,idx,v);print(key,idx,report(p),flush=True)
  cert[key]={'shifts':[3,1,1,3],'coefficients':[[list(m),str(c)]for m,c in sorted(p.items())]}
 (R/'laurent_cone_certificate.json').write_text(json.dumps(cert))
if __name__=='__main__':main()
