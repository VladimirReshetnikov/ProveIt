#!/usr/bin/env python3
"""Independent exact reciprocal composition audit; imports no producer."""
import argparse,copy,hashlib,json,math,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SIGNED=ROOT.parent/'signed'
binding=json.loads((ROOT/'SOURCE_BINDING.json').read_text())
if binding['relative_component']!='../signed':raise ValueError('noncanonical signed component')
manifest=SIGNED/'MANIFEST_SHA256.json'
if not manifest.is_file():raise ValueError('Extract both ordinary archive parts beside each other: reciprocal212 requires sibling signed/')
if hashlib.sha256((SIGNED/'stages/weighted_source/equation.json').read_bytes()).hexdigest()!=binding['equation_sha256']:raise ValueError('wrong weighted source')
if hashlib.sha256(manifest.read_bytes()).hexdigest()!=binding['manifest_sha256']:raise ValueError('wrong frozen signed manifest')
for relative,expected in json.loads(manifest.read_text()).items():
 if Path(relative).is_absolute()or'..'in Path(relative).parts:raise ValueError('unsafe signed manifest path')
 if hashlib.sha256((SIGNED/relative).read_bytes()).hexdigest()!=expected:raise ValueError('signed source mismatch: '+relative)
sys.path.insert(0,str(SIGNED/'code'))
import operations_audit as A,audit_projection as P

def need(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):
 p=str(p);base=SIGNED if p.startswith('inherited_signed/')else ROOT;p=p.removeprefix('inherited_signed/');return json.loads((base/p).read_text())
def digest(x):return hashlib.sha256((json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()
def rows(e):return[A.collect(r['terms'])for r in e['residuals']]
def val(p,x):
 out=0
 for m,c in p.items():
  for i in m:c*=x[i]
  out+=c
 return out

def chart_check(target=None):
 old=read('inherited_signed/stages/weighted_source/equation.json');new=target or read('stages/source.json');names=[v['name']for v in old['variables']];i=names.index('pow2.output')
 expected=[A.substitute(p,i,{(i,):3,():2})for p in rows(old)];ns=copy.deepcopy(old['variables']);ns[i]['name']='radix.chart_q_third'
 need(new['variables']==ns and rows(new)==expected,'exact q chart substitution');need([r['label']for r in old['residuals']]==[r['label']for r in new['residuals']],'retained rows');return new

def merge_check(parent,certificate,target):
 n=len(parent['variables']);pr=rows(parent);need(certificate['input_sha256']==digest(parent),'pool source pin');need(certificate['output_sha256']==digest(target),'pool output pin');removed=set();dropped=set();groups=[]
 def coeff(p,i):
  out={}
  for m,c in p.items():
   need(m.count(i)<=1,'nonlinear private coordinate')
   if i in m:out[tuple(v for v in m if v!=i)]=c
  return out
 for g in certificate['groups']:
  K,L=g['K'],g['L'];aidx,bidx=g['aggregate_row'],g['norm_row'];ar,br=pr[aidx],pr[bidx]
  need(parent['variables'][K]['name']==g['group']+'.K'and parent['variables'][L]['name']==g['group']+'.L','private variable names')
  need(coeff(ar,K)=={():1}and coeff(br,L)=={():1},'unit coefficients')
  base={m:-c for m,c in coeff(br,K).items()};aa=coeff(ar,L);M={m:c for m,c in ar.items()if K not in m and L not in m};S={m:c for m,c in br.items()if K not in m and L not in m}
  need(ar==A.linear(A.linear({(K,):1},A.multiply(aa,{(L,):1}),1),M,1),'aggregate form');need(br==A.linear(A.linear(S,A.multiply(base,{(K,):1}),-1),{(L,):1},1),'norm form')
  T=A.linear({():-1},A.multiply(base,aa),-1);E=A.linear(S,A.multiply(base,M),1)
  for key,p in [('base',base),('a',aa),('T',T),('E',E)]:need(A.collect(g[key])==p,'pool formula '+key)
  need(A.linear(E,A.multiply(T,{(L,):1}),-1)==A.linear(br,A.multiply(base,ar),1),'pool elimination identity')
  groups.append((base,aa,E,T,K,L,ar,br));removed.update([K,L]);dropped.update([aidx,bidx])
 need(len(groups)==2 and len(removed)==4 and len(dropped)==4,'pool census');need(sorted(removed)==certificate['removed_variables']and sorted(dropped)==certificate['removed_rows'],'deletion lists')
 for j,p in enumerate(pr):
  if j not in dropped:need(all(not set(m)&removed for m in p),'outside occurrence of removed coordinate')
 base0,a0,E0,T0,K0,L0,ar0,br0=groups[0];base1,a1,E1,T1,K1,L1,ar1,br1=groups[1]
 need(A.linear(base1,base0,-1)=={():1},'consecutive bases');need(A.linear(base0,a0,-1)==A.linear(base1,a1,-1)==A.collect(certificate['two_A_original']),'common Pell parameter')
 qidx=next(i for i,v in enumerate(parent['variables'])if v['name']=='radix.chart_q_third');need(base0=={(qidx,):3,():1},'safe q congruence class')
 prod=A.multiply(T0,T1);rp=A.linear(A.linear(A.multiply(E0,T1),A.multiply(E1,T0),1),A.multiply({(n,):1},prod),-1)
 need(A.collect(certificate['new_residual_original_indices'])==rp,'literal merged residual')
 # Global polynomial forward identity, including old private witnesses.
 forward=A.substitute(rp,n,{(L0,):1,(L1,):1})
 identity=A.linear(A.multiply(T1,A.linear(br0,A.multiply(base0,ar0),1)),A.multiply(T0,A.linear(br1,A.multiply(base1,ar1),1)),1)
 need(forward==identity,'forward witness ideal identity')
 keep=[i for i in range(n)if i not in removed];need(keep==certificate['retained_old_indices'],'retained coordinates');ren={v:i for i,v in enumerate(keep)};ren[n]=len(keep)
 remap=lambda p:{tuple(ren[i]for i in m):c for m,c in p.items()};expected=[remap(p)for j,p in enumerate(pr)if j not in dropped]+[remap(rp)]
 need(rows(target)==expected,'all final residuals');need(target['variables']==[parent['variables'][i]for i in keep]+[{'kind':'reciprocal_pool','name':'reciprocal.z'}],'all final variables')
 expansion={}
 for p in expected:expansion=A.linear(expansion,A.multiply(p,p),1)
 need(A.collect(read('equations/expanded_polynomial.json')['terms'])==expansion,'full expansion')
 metric={'variables':len(target['variables']),'residuals':len(expected),'degree':max(map(len,expansion)),'collected_terms':len(expansion),'coefficient_height':max(map(abs,expansion.values())),'maximum_residual_degree':max(len(m)for p in expected for m in p),'residual_terms':sum(map(len,expected)),'residual_height':max(abs(c)for p in expected for c in p.values()),'all_coordinates_used':{i for m in expansion for i in m}==set(range(len(target['variables'])))}
 need(metric==read('equations/metrics.json'),'metrics');return metric

def arithmetic_controls():
 count=0
 for t in range(3,61,3):
  f=3
  while f<=t:f*=3
  need(math.comb(f+t,t)%3==1,'binomial mod3 fixture');count+=1
 for N in [5,7,11,13]:
  for residue in range(N*N):
   chosen=next(residue+k*N*N for k in range(1,7)if(residue+k*N*N)%2==0 and(2+4*(residue+k*N*N+17))%3!=0)
   need(chosen% (N*N)==residue,'CRT residue fixture')
 return {'binomial_mod3_fixtures':count,'CRT_parity_and_mod3_fixtures':sum(N*N for N in [5,7,11,13]),'scope':'finite controls only; unbounded proof is PROOF.md'}

def chart_comparisons():
 e=read('equations/equation.json');i=next(j for j,v in enumerate(e['variables'])if v['name']=='radix.chart_q_third');out=[]
 need(i==95,'comparison coordinate')
 for control in read('CHART_COMPARISON.json')['controls']:
  rs=[A.substitute(p,i,A.collect(control['replacement']))for p in rows(e)];exp={}
  for p in rs:exp=A.linear(exp,A.multiply(p,p),1)
  actual={'monomials':len(exp),'height':max(map(abs,exp.values())),'row_height':max(abs(c)for p in rs for c in p.values())}
  need(all(actual[k]==control[k]for k in actual),'chart comparison '+control['name']);out.append(dict(name=control['name'],**actual))
 return out

def run(deep=False):
 if (ROOT/'MANIFEST_SHA256.json').exists():
  for f,h in read('MANIFEST_SHA256.json').items():need(hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,'manifest '+f)
 src=chart_check();e=copy.deepcopy(src)
 for v in e['variables']:
  if v['name']=='growth.F':v['name']='crt.growth_majorant_F'
 ns,rs,counts=A.replay(e['variables'],rows(e),read('stages/transport_operations.json'));e=read('stages/transport.json');need(e['variables']==ns and rows(e)==rs,'transport identities')
 for cert in read('stages/radical_certificate.json')['steps']:e=P.one_step(e,cert)
 need(e==read('stages/radical.json'),'radical identities');parent=read('stages/pool_parent.json');need(parent['variables']==e['variables']and rows(parent)==rows(e),'metadata-only pool labels')
 certificate=read('equations/certificate.json');target=read('equations/equation.json');metric=merge_check(parent,certificate,target);controls=[]
 bad=copy.deepcopy(src);bad['residuals'][0]['terms'][0][0]+=1
 try:chart_check(bad)
 except ValueError:controls.append('chart_coefficient')
 else:raise ValueError('corrupt chart accepted')
 bad=copy.deepcopy(certificate);bad['groups'][0]['T'][0][0]+=1
 try:merge_check(parent,bad,target)
 except ValueError:controls.append('modulus_coefficient')
 else:raise ValueError('corrupt modulus accepted')
 bad=copy.deepcopy(target);bad['residuals'][-1]['terms'][0][0]+=1
 try:merge_check(parent,certificate,bad)
 except ValueError:controls.append('merged_residual_coefficient')
 else:raise ValueError('corrupt final residual accepted')
 command=[sys.executable,'-B']+(['-O']if sys.flags.optimize else[]);replays={}
 for script,args in [(ROOT/'build.py',['--check'])]+([(SIGNED/'verify.py',['--deep'])]if deep else[]):
  z=subprocess.run(command+[str(script)]+args,capture_output=True,text=True,cwd=script.parent);need(z.returncode==0,z.stdout+'\n'+z.stderr);replays[('signed/'+script.name if script.parent==SIGNED else str(script.relative_to(ROOT)))]=json.loads(z.stdout)
 return {'status':'PASS','optimized':bool(sys.flags.optimize),'deep':deep,'metrics':metric,'chart_operations':counts,'radical_projections':2,'independent_forward_pool_identity':True,'negative_controls':controls,'arithmetic_controls':arithmetic_controls(),'chart_comparisons':chart_comparisons(),'reconstruction':replays,'scope':'finite identities and full coefficients, composed with the separate ordinary cofinal restriction and reciprocal theorem'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--deep',action='store_true');ap.add_argument('--receipt',type=Path);args=ap.parse_args();result=run(args.deep)
 if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
