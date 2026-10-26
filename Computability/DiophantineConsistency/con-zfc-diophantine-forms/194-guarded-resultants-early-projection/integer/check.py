#!/usr/bin/env python3
"""Independent standard-library checker: imports neither producer nor polynomial module."""
from pathlib import Path
from collections import Counter
import ast,copy,hashlib,json,re,sys
ROOT=Path(__file__).resolve().parent
D=524288

def fail(ok,msg):
 if not ok:raise ValueError(msg)
def read(p):return json.loads((ROOT/p).read_text())
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def poly(ts):
 c=Counter()
 for a,m in ts:c[tuple(sorted(m))]+=a
 return {m:a for m,a in c.items()if a}
def add(*args):
 c=Counter()
 for p in args:
  for m,a in p.items():c[m]+=a
 return {m:a for m,a in c.items()if a}
def scale(p,a):return {m:a*c for m,c in p.items()if a*c}
def mul(a,b):
 c=Counter()
 for m,v in a.items():
  for n,w in b.items():c[tuple(sorted(m+n))]+=v*w
 return {m:a for m,a in c.items()if a}
def var(i):return {(i,):1}
def const(a):return {():a}if a else{}
def sq(p):return mul(p,p)
def sub(p,q):return add(p,scale(q,-1))
def substitute(p,i,q):
 out={}
 for m,a in p.items():
  term=const(a)
  for j in m:term=mul(term,q if j==i else var(j))
  out=add(out,term)
 return out
def terms(p):return [[a,list(m)]for m,a in sorted(p.items())]
def metric(eq,rs):
 out=add(*(sq(p)for p in rs))
 return {'variables':len(eq['variables']),'rows':len(rs),'residual_terms':sum(map(len,rs)),'row_height':max(abs(a)for p in rs for a in p.values()),'degree':max(map(len,out)),'monomials':len(out),'height':max(map(abs,out.values()))},out


def expected():
 e=read('sources/parent210.json');fail(hashlib.sha256((ROOT/'sources/parent210.json').read_bytes()).hexdigest()=='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a','parent pin')
 old=[poly(r['terms'])for r in e['residuals']];v=var;c=const
 fail(len(e['variables'])==210 and len(old)==150,'source dimensions')
 fail(old[125]==add(v(0),c(-16),scale(sq(v(178)),-4)),'horizon source row')
 fail(all(178 not in m for i,r in enumerate(old)if i!=125 for m in r),'private horizon root')
 t=add(scale(v(0),4),c(2));rs=[substitute(r,0,t)for r in old];keep=[i for i in range(210)if i!=178];rkeep=[i for i in range(150)if i!=125];ren={i:j for j,i in enumerate(keep)}
 target=[{tuple(ren[j]for j in m):a for m,a in rs[i].items()}for i in rkeep]
 atoms=[('t',v(0)),('t+1',add(v(0),c(1))),('F+t',add(v(2),v(0))),('x',v(1)),('obsolete_growth_base_duplicate',v(0)),('B',v(3)),('F',v(2)),('y+1',v(4)),('a',v(8))]
 atoms += [(name,v(i))for name,i in zip(['b','c','d','S','Sp','u','vq'],range(9,16))]
 atoms += [('C',scale(v(16),2)),('N',v(17)),('q',add(v(94),c(-1))),('q+1',v(94)),('affine_radix_base',add(scale(v(16),4),scale(v(2),2),c(2)))]
 atoms += [('pow'+str(k)+'.output',v(i))for k,i in [(3,95),(4,96),(5,100),(7,103),(8,106),(9,109),(10,112),(11,113),(12,116),(13,119),(14,120),(15,124),(16,127)]]
 fail(old[124]==add(v(130),c(-2),*(scale(sq(a),-1)for _,a in atoms)),'whole original actual frame')
 actual=[(name,substitute(a,0,t))for name,a in atoms]
 fail(rs[124]==add(v(130),c(-2),*(scale(sq(a),-1)for _,a in actual)),'whole changed actual frame')
 q=add(v(94),c(-1));rad=add(scale(v(16),4),scale(v(2),2),c(2))
 requests=[(v(3),v(1),v(17)),(rad,v(1),q)]
 requests += [(v(94),k,v(i))for k,i in [(add(v(2),v(0)),95),(v(8),100),(v(9),103),(v(10),106),(v(11),109),(v(12),112),(v(13),116),(v(14),119),(v(15),124),(scale(v(16),2),127)]]
 requests += [(q,k,v(i))for k,i in [(v(0),96),(v(4),113),(v(1),120)]]
 fail(len(requests)==15 and all(a in [b for _,b in atoms]for r in requests for a in r),'45 actual ports covered')
 fail(old[147]==sub(v(208),mul(v(0),v(2))),'growth product source')
 fail(old[148]==add(sq(v(207)),scale(sq(v(208)),-16),scale(mul(v(208),v(2)),-8),c(-1)),'unchanged center4t+1')
 fail(old[149]==sub(v(2),scale(mul(v(0),add(scale(v(209),2),c(1))),D)),'growth odd divisibility source')
 fail(rs[147]==sub(v(208),mul(t,v(2))),'actual changed growth product')
 fail(rs[149]==sub(v(2),scale(mul(t,add(scale(v(209),2),c(1))),D)),'actual changed growth divisibility')
 # An inverse polynomial identity over Q; on physical tuples t=2 mod4 it is integral.
 from fractions import Fraction
 inverse=add(scale(v(0),Fraction(1,4)),c(Fraction(-1,2)))
 fail(all(substitute(rs[i],0,inverse)==old[i]for i in rkeep),'all retained affine inverse identities')
 return e,old,rs,target,atoms,actual,keep,rkeep,ren

def verify_bundle(b):
 e,old,rs,target,atoms,actual,keep,rkeep,ren=expected();cert=b['certificate'];eq=b['equation'];frame=b['frame'];mp=b['mapping']
 fail(cert['source']=='sources/parent210.json'and cert['source_sha256']==hashlib.sha256((ROOT/'sources/parent210.json').read_bytes()).hexdigest(),'relative source binding')
 fail(cert['old_horizon']==terms(old[125]) and cert['source_frame_row']==124 and cert['source_growth_rows']==[147,148,149],'source row certificate')
 fail(cert['actual_t']==terms(add(scale(var(0),4),const(2)))and cert['deleted_coordinate']==178 and cert['deleted_row']==125,'horizon certificate')
 fail(cert['retained_old_coordinates']==keep and cert['retained_old_rows']==rkeep and cert['old_to_new']==[[i,j]for i,j in ren.items()],'complete maps')
 edits=[{'old_row':i,'label':e['residuals'][i]['label'],'before':terms(old[i]),'after_before_renumbering':terms(rs[i])}for i in rkeep if rs[i]!=old[i]]
 fail(cert['changed_retained_rows']==edits,'all changed rows')
 fail(mp['actual_t']==cert['actual_t']and mp['retained_old_coordinates']==keep and mp['retained_old_rows']==rkeep and mp['old_to_new']==cert['old_to_new'],'coordinate map')
 fail(frame['atoms']==[{'label':name,'parent_terms':terms(a),'actual_terms':terms(b)}for(name,a),(_,b)in zip(atoms,actual)],'complete frame ledger')
 fail(frame['constant']==2 and frame['old_frame']==terms(old[124])and frame['new_frame']==terms(rs[124])and frame['power_requests']==15 and frame['power_ports']==45,'frame certificate')
 fail(eq['domain']=='unrestricted integers'and len(eq['variables'])==209 and eq['polynomial']=='sum(square(row) for row in residuals)','literal unrestricted domain')
 fail([poly(r['terms'])for r in eq['residuals']]==target,'all final residuals')
 fail(all(len(m)<=2 for p in target for m in p),'quadratic residuals')
 fail({i for p in target for m in p for i in m}==set(range(209)),'all209variables live')
 met,pp=metric(eq,target)
 fail(b['metrics']==met,'metrics');fail(b['expansion']=={'schema':'sparse_integer_polynomial_v1','variables':209,'terms':terms(pp)},'every quartic coefficient')
 return {'status':'PASS','metrics':met,'changed_retained_rows':len(edits),'retained_inverse_identities':149,'actual_frame_atoms':len(atoms),'actual_power_ports':45,'frame_fully_reconstructed':True}

def parse_expression(text):
 def rec(node):
  if isinstance(node,ast.Constant)and type(node.value)is int:return const(node.value)
  if isinstance(node,ast.Name)and re.fullmatch(r'x[0-9]+',node.id):return var(int(node.id[1:]))
  if isinstance(node,ast.UnaryOp)and isinstance(node.op,ast.USub):return scale(rec(node.operand),-1)
  if isinstance(node,ast.UnaryOp)and isinstance(node.op,ast.UAdd):return rec(node.operand)
  if isinstance(node,ast.BinOp):
   if isinstance(node.op,ast.Add):return add(rec(node.left),rec(node.right))
   if isinstance(node.op,ast.Sub):return sub(rec(node.left),rec(node.right))
   if isinstance(node.op,ast.Mult):return mul(rec(node.left),rec(node.right))
   if isinstance(node.op,ast.Pow)and isinstance(node.right,ast.Constant)and node.right.value==2:return sq(rec(node.left))
  raise ValueError('forbidden literal expression')
 return rec(ast.parse('('+text.strip()+')',mode='eval').body)
def check_prints(eq):
 expected=[poly(r['terms'])for r in eq['residuals']]
 lines=[s for s in (ROOT/'integer209/residuals.txt').read_text().splitlines()if re.match(r'^R[0-9]+ =',s)]
 fail(len(lines)==149,'text row count')
 for i,line in enumerate(lines):
  head,body=line.split('=',1);fail(head.strip()=='R'+str(i),'text row index');fail(parse_expression(body)==expected[i],'parsed text coefficient '+str(i))
 tex=(ROOT/'integer209/residuals.tex').read_text()
 blocks=re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}',tex,re.S)
 fail(len(blocks)==149,'TeX row count')
 for i,block in enumerate(blocks):
  head,body=block.split('=',1);fail(head.strip()=='R_{'+str(i)+'}','TeX row index')
  body=body.replace('&','').replace('{}','').replace('\\\\','')
  body=re.sub(r'x_\{([0-9]+)\}',r'x\1',body)
  body=re.sub(r'\^\{([0-9]+)\}',r'**\1',body)
  body=re.sub(r'(x[0-9]+(?:\*\*[0-9]+)?)(?=x)',r'\1*',body)
  body=re.sub(r'([0-9])\s+(?=x)',r'\1*',body)
  fail(parse_expression(body)==expected[i],'parsed TeX coefficient '+str(i))
 return {'plain_rows_parsed':149,'tex_rows_parsed':149}

def main():
 b={'certificate':read('semantic_certificate.json'),'mapping':read('coordinate_map.json'),'frame':read('frame_certificate.json'),'equation':read('integer209/equation.json'),'expansion':read('integer209/expanded_polynomial.json'),'metrics':read('integer209/metrics.json')}
 r=verify_bundle(b);r['printed_residuals']=check_prints(b['equation'])
 mutations=[('wrong horizon',lambda a:a['certificate']['actual_t'][0].__setitem__(0,3)),('wrong root',lambda a:a['certificate'].__setitem__('deleted_coordinate',177)),('wrong row',lambda a:a['certificate'].__setitem__('deleted_row',124)),('changed row',lambda a:a['certificate']['changed_retained_rows'][0]['after_before_renumbering'][0].__setitem__(0,999)),('frame atom',lambda a:a['frame']['atoms'][0]['actual_terms'][0].__setitem__(0,1)),('frame constant',lambda a:a['frame'].__setitem__('constant',3)),('map',lambda a:a['mapping']['retained_old_coordinates'].__setitem__(0,1)),('domain',lambda a:a['equation'].__setitem__('domain','natural numbers')),('literal row',lambda a:a['equation']['residuals'][0]['terms'][0].__setitem__(0,999)),('quartic',lambda a:a['expansion']['terms'][0].__setitem__(0,999)),('metric',lambda a:a['metrics'].__setitem__('height',1)),('absolute path',lambda a:a['certificate'].__setitem__('source','/tmp/parent210.json'))]
 rejected=[]
 for name,f in mutations:
  bad=copy.deepcopy(b);f(bad)
  try:verify_bundle(bad)
  except (ValueError,KeyError,IndexError):rejected.append(name)
  else:raise ValueError('accepted corruption '+name)
 r.update(optimized=bool(sys.flags.optimize),rejected_actual_corruptions=rejected);print(json.dumps(r,indent=2,sort_keys=True))
if __name__=='__main__':main()
