#!/usr/bin/env python3
"""Independent complete finite algebra checks. Imports no equation producer.

The mathematical cap, power, factorial and calculus proofs are separate.
These checks authenticate syntax and replay every algebraic restoration.
"""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import argparse,json,subprocess,sys,tempfile
from check_natural import verify as natural_verify

HERE=Path(__file__).resolve().parent
def need(c,m):
 if not c:raise ValueError(m)
def read(p):return json.loads(Path(p).read_text())
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def collect(terms):
 out={}
 for c,m in terms:
  k=tuple(sorted(m));out[k]=out.get(k,0)+c
 return {m:c for m,c in out.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def mul(p,q):return collect([(a*b,ma+mb) for ma,a in p.items() for mb,b in q.items()])
def subst(p,v,r):
 out=[]
 for m,c in p.items():
  q={():c}
  for x in m:q=mul(q,r if x==v else {(x,):1})
  out+=list((c,m) for m,c in q.items())
 return collect(out)
def deg(p):return max(map(len,p),default=0)
def expand(e):
 out=[]
 for r in e['residuals']:
  p=collect(r['terms']);out+=list((c,m) for m,c in mul(p,p).items())
 return terms(collect(out))
def integer_projection(source,target,c):
 need(sha256(canon(source)).hexdigest()==c['input_sha256'],'integer projection source hash')
 need(sha256(canon(target)).hexdigest()==c['output_sha256'],'integer projection target hash')
 rows={i:collect(r['terms']) for i,r in enumerate(source['residuals'])};live=set(range(len(source['variables'])))
 for st in c['steps']:
  i,v=st['row_id'],st['variable'];r=collect(st['restoration'])
  need(i in rows and v in live,'live monic deletion')
  need(all(x in live and x!=v for m in r for x in m),'live restoration coordinates')
  need(deg(r)<=2,'restoration quadratic')
  expected=collect([(1,[v])]+[(-a,m) for m,a in r.items()])
  need(rows[i]==expected or rows[i]=={m:-a for m,a in expected.items()},'exact signed monic identity')
  del rows[i]
  for j,p in list(rows.items()):
   q=subst(p,v,r);need(deg(q)<=2,'quadratic degree preserved')
   if q:rows[j]=q
   else:del rows[j]
  live.remove(v)
 used=sorted({v for p in rows.values() for m in p for v in m});mapping={v:i for i,v in enumerate(used)}
 need(used==c['retained_original_variables'],'all retained coordinates')
 need(sorted(live-set(used))==c['unconstrained_removed'],'unused zero restorations')
 need(sorted(rows)==c['retained_original_rows'],'all surviving rows')
 need([source['variables'][v] for v in used]==target['variables'],'variable ordering')
 expected=[{'label':source['residuals'][i]['label'],'terms':[[a,[mapping[v] for v in m]] for m,a in sorted(p.items())]} for i,p in sorted(rows.items())]
 need(expected==target['residuals'],'all projected residual coefficients')
 return len(c['steps'])
def verify_signs(source,guarded,c):
 n=len(source['variables']);rows=[collect(r['terms']) for r in source['residuals']]
 need(guarded['variables'][:n]==source['variables'] and guarded['residuals'][:len(rows)]==source['residuals'],'unchanged full source body')
 guardset=c['signs']['guard_indices'];need(len(guardset)==len(set(guardset)),'distinct scalar guards')
 nextv=n;nextr=len(rows)
 for v in guardset:
  a,b,d=range(nextv,nextv+3);expected=collect([[1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[d,d]],[-1,[d]]])
  need(collect(guarded['residuals'][nextr]['terms'])==expected,'exact scalar Legendre graph')
  nextv+=3;nextr+=1
 for p in c['paired_remainders']:
  r,s=p['pair'];row=rows[p['row']]
  need(collect(terms(row)+[[1,[r]],[1,[s]],[1,[]]])==collect(p['denominator']),'literal positive-sum pair identity')
  a,b,d=range(nextv,nextv+3);expected=collect([[1,[r,s]],[-1,[a,a]],[-1,[b,b]],[-1,[d,d]],[-1,[d]]])
  need(p['guard_row']==nextr and p['auxiliary']==[a,b,d],'pair private layout')
  need(collect(guarded['residuals'][nextr]['terms'])==expected,'exact pair Legendre graph')
  nextv+=3;nextr+=1
 need(nextv==len(guarded['variables']) and nextr==len(guarded['residuals']),'complete guard layout')
 # Every sign-inference step is an exact positive-monomial or affine-square
 # identity. The semantic axioms are added only after checking the prefix.
 checked=[]
 for st in c['signs']['proof_steps']:
  v,rid,a=st['variable'],st['row'],st['coefficient'];rhs=collect(st['rhs'])
  need(type(a)is int and a>0,'positive sign coefficient')
  p=collect([(a,[v])]+[(-x,m) for m,x in rhs.items()]);row=rows[rid]
  need(row==p or row=={m:-x for m,x in p.items()},'literal sign identity')
  if st['kind']=='positive_monomials':
   need(all(x>0 for x in rhs.values()),'positive monomial coefficients')
   deps={k for m in rhs for k,power in Counter(m).items() if power%2}
  elif st['kind']=='affine_square':
   root=collect(st['square_root']);need(deg(root)<=1 and mul(root,root)==rhs,'exact affine square sign')
   deps=set()
  else:raise ValueError('unknown sign inference rule')
  need(deps==set(st['dependencies']),'complete sign dependencies');checked.append(st)
 def closure(seed):
  known=set(seed);used=[]
  for st in checked:
   if set(st['dependencies'])<=known:known.add(st['variable']);used.append(st)
  return known,used
 prefix,used=closure(guardset)
 need(prefix==set(c['prefix_known']) and used==c['prefix_steps'],'exact noncircular sign prefix')
 need(set(c['prefix_required'])<=prefix,'ordinary cap prerequisites before root recovery')
 semantic=c['seed_X']+c['seed_Y']+c['deferred_quotients_and_moduli']+c['deferred_output_slacks']+[v for p in c['paired_remainders'] for v in p['pair']]
 after,_=closure(guardset+semantic)
 need(after==set(range(n)),'every original natural coordinate restored')
 need(len(c['seed_X'])==len(c['seed_Y'])==15,'all fifteen principal pairs')
 return {'scalar_guards':len(guardset),'product_guards':len(c['paired_remainders']),'sign_identities':len(checked),'prefix_nonnegative_coordinates':len(prefix)}
def run():
 led=read(HERE/'SOURCE_LEDGER.json')
 for p,h in led['files'].items():need(sha256((HERE/p).read_bytes()).hexdigest()==h,'inherited source byte hash '+p)
 d=HERE/'natural242';source=read(d/'raw/equation.json');target=read(d/'natural/equation.json');cert=read(d/'natural/elimination_certificate.json')
 nr,exp=natural_verify(source,target,cert)
 need(exp==read(d/'natural/expanded_polynomial.json')['terms'],'complete natural quartic expansion')
 d=HERE/'integer378';original=read(d/'natural_raw/equation.json');body=read(d/'source.json');guarded=read(d/'guarded.json');c=read(d/'signed_certificate.json')
 need(original['variables']==body['variables'] and original['residuals']==body['residuals'],'signed source is complete same natural row system')
 sg=verify_signs(body,guarded,c)
 projected=read(d/'projected.json');pc=read(d/'projection_certificate.json');steps=integer_projection(guarded,projected,pc)
 final=read(d/'equation.json');tr=read(d/'translation_certificate.json');shifts=dict(tr['shifts'])
 need(projected['variables']==final['variables'],'translation variable ordering')
 expected=[]
 for row in projected['residuals']:
  p=collect(row['terms'])
  for v,s in shifts.items():p=subst(p,v,{(v,):1,():s})
  expected.append({'label':row['label'],'terms':terms(p)})
 need(expected==final['residuals'],'complete integral translation')
 exp=expand(final);need(exp==read(d/'expanded_polynomial.json')['terms'],'complete integer quartic expansion')
 met={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for _,m in exp),'monomials':len(exp),'height':max(abs(a) for a,_ in exp),'scalar_guards':sg['scalar_guards'],'product_guards':sg['product_guards']}
 need(met==read(d/'METRICS.json'),'exact integer census')
 # Three algebraic controls target independent stages, not just hashes.
 bad=deepcopy(pc);bad['steps'][0]['restoration'][0][0]+=1
 try:integer_projection(guarded,projected,bad)
 except ValueError:pass
 else:raise ValueError('corrupted inverse accepted')
 bad=deepcopy(c);bad['signs']['proof_steps'][0]['rhs'][0][0]+=1
 try:verify_signs(body,guarded,bad)
 except ValueError:pass
 else:raise ValueError('corrupted sign identity accepted')
 bad=deepcopy(c);bad['paired_remainders'][0]['pair'][0]+=1
 try:verify_signs(body,guarded,bad)
 except ValueError:pass
 else:raise ValueError('corrupted pair interface accepted')
 return {'status':'PASS','natural242':nr,'integer378':met,'signed_inverse_steps':steps,'integer_signs':sg,'corruption_controls_rejected':3,'source_files_authenticated':len(led['files']),'scope':'Complete finite integer/natural restoration and coefficient checks; unbounded meaning is supplied by the ordinary proofs, not finite tests.'}
def rebuild():
 compared=[]
 with tempfile.TemporaryDirectory(prefix='merged-cap-rebuild-') as td:
  t=Path(td)
  cmds=[['build_capped_modular.py','--out',str(t/'natural242'),'--syntax','xx0','--cap','16','--merged'],['build_capped_modular.py','--out',str(t/'fullroot'),'--syntax','xx0','--cap','16','--merged','--recover-x'],['build_signed_merged.py','--source',str(t/'fullroot/raw/equation.json'),'--out',str(t/'integer378'),'--defer-quotients','--pair-guards']]
  for cmd in cmds:
   proc=subprocess.run([sys.executable,'-B']+(['-O'] if not __debug__ else [])+[str(HERE/cmd[0])]+cmd[1:],capture_output=True,text=True)
   need(proc.returncode==0,'rebuild failed: '+proc.stderr)
  for src,dest in [(t/'natural242',HERE/'natural242'),(t/'fullroot/raw',HERE/'integer378/natural_raw'),(t/'integer378',HERE/'integer378')]:
   for p in src.rglob('*.json'):
    q=dest/p.relative_to(src);need(q.exists() and p.read_bytes()==q.read_bytes(),'byte-exact rebuild '+str(q));compared.append(str(q.relative_to(HERE)))
 return {'rebuilt_json_files_compared':len(compared),'all_bytes_identical':True}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--rebuild',action='store_true');ap.add_argument('--output',type=Path);a=ap.parse_args()
 result=run();result['python_optimized']=not __debug__
 if a.rebuild:result['rebuild']=rebuild()
 output=json.dumps(result,indent=2,sort_keys=True)+'\n'
 if a.output:a.output.write_text(output)
 print(output,end='')
