"""Owned14 precise closed-interval source crossover prices, no table compiler."""
from pathlib import Path
import sys,json,hashlib,time
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
P=ROOT/'latest218_baseline/candidate-k218';Q=ROOT/'research217_review/contextual/selected/machine'
roots=[A.P.tree(json.load(open(x/'sites218.json')))for x in(P,Q)];tables=[A.R.table(x/'k218.native.tm')for x in(P,Q)];groups=[];paths=[]
for T,t in zip(tables,roots):g,p,e=A.P.allocation(T,t);groups.append(g);paths.append(p)
rows=json.load(open(OUT/'CROSSOVER_INTERVAL_INVENTORY.json'))['rows'];wanted=[(486,648),(1178,1340),(3678,4330),(4567,4597),(4652,4744),(121,648),(648,4597)];selected=[next(r for r in rows if tuple(r['interval'])==w)for w in wanted]
start=time.monotonic();reports=[]
for r in selected:
 for side in(0,1):
  src=roots[side];donor=roots[1-side];k=('primary','alternate');p=r[k[side]+'_path'];q=r[k[1-side]+'_path'];old=A.at(src,p);new=A.at(donor,q)
  assert A.boundary(old)==A.boundary(new)==(0,0,False)
  out=A.replace(src,p,new);ss=A.flatten(out);cfg=A.continuation_cfg(out);assert cfg==A.continuation_cfg(src)==A.address_cfg(ss);assert[x[1:]for x in ss]==[x[1:]for x in A.flatten(src)]
  before=A.P.nodes(src);after=A.P.nodes(out);removed=before-after;added=after-before
  def meta(n):return dict(leaves=A.length(n),ast_sha256=hashlib.sha256(repr(n).encode()).hexdigest(),recipient_entries=sorted(z for z,ns in groups[side].items()if n in ns),donor_entries=sorted(z for z,ns in groups[1-side].items()if n in ns))
  raw=A.compact(ss);H=hashlib.sha256(raw).hexdigest();dest=OUT/'crossovers';dest.mkdir(exist_ok=True);(dest/(H[:16]+'.sites.json')).write_bytes(raw)
  reports.append(dict(interval=r['interval'],recipient=k[side],source_sha256=H,source_file=str(dest.relative_to(ROOT)/(H[:16]+'.sites.json')),source_nodes=len(after)+23,delta_internal_nodes=len(added)-len(removed),removed_roles=[meta(n)for n in sorted(removed,key=lambda n:(A.length(n),repr(n)))],added_roles=[meta(n)for n in sorted(added,key=lambda n:(A.length(n),repr(n)))],exact_primitive_word=True,dual_cfg_equal=True,recipient_path=p,donor_path=q))
data=dict(reports=reports,seconds=time.monotonic()-start,scope='Fourteen exact source substitutions only. All retain ordered primitive op/args and both CFG resolutions. Source DAG and role correspondences do not establish physical allocation or new selector opportunities; no table produced.')
(OUT/'CROSSOVER_PRICES.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps([{k:v for k,v in r.items()if k not in('removed_roles','added_roles')}|dict(removed=[(x['leaves'],x['recipient_entries'])for x in r['removed_roles']],added=[(x['leaves'],x['donor_entries'])for x in r['added_roles']])for r in reports],indent=2));print('seconds',data['seconds'])
# Save the literal30-leaf difference for the scanner lane.
r=next(r for r in rows if r['interval']==[4567,4597]);n=A.at(roots[0],r['primary_path']);m=A.at(roots[1],r['alternate_path']);a,b=n[0];c=n[1];assert m==(a,(b,c));assert all(A.boundary(x)==(0,0,False)for x in(a,b,c))
(OUT/'CROSSOVER_30_BLOCK.json').write_text(json.dumps(dict(interval=[4567,4597],primary=n,alternate=m,factor_leaves=list(map(A.length,(a,b,c))),factors=[a,b,c],primitive_word=A.flatten(n),scope='Exact closed right rotation, not identified as an equality test by this receipt.'),indent=2)+'\n')
