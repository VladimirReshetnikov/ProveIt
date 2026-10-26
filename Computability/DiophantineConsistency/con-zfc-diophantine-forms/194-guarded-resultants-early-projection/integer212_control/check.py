#!/usr/bin/env python3
"""Independent standard-library checker: imports neither producer nor polynomial module."""
from pathlib import Path
from collections import Counter
import ast,copy,hashlib,json,re,sys
ROOT=Path(__file__).resolve().parent
D=1048576

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
 parent=read('sources/parent213.json');old=[poly(r['terms'])for r in parent['residuals']]
 fail(hashlib.sha256((ROOT/'sources/parent213.json').read_bytes()).hexdigest()=='48b84f5c37082b6575cd0b4f4bdae9baeaa5e1e6fbaea83004f62cfba6ce954b','source byte pin')
 v=var;c=const;t=v(0);F=v(2);A=add(v(131),c(1));d=add(scale(t,4),c(2));w=v(180);z=v(181);Z=v(182)
 starts=[135,144,147,150,153,156,159,162,165,168,171,174,177,180]
 nominal=[t,add(t,F),add(v(8),c(-1)),v(9),v(10),v(11),v(12),v(4),v(13),v(14),v(1),v(15),scale(v(16),2),scale(t,D)]
 normrows=[95,103,105,107,109,111,113,115,117,119,121,123,125,127]
 pairs=[];raw={}
 for start,k,nr in zip(starts,nominal,normrows):
  X=add(v(start),v(start+2),c(1)if start==171 else{})
  Y=add(v(start+1),c(-1)if start==147 else{})
  AY=add(v(start+2),c(1)if start==171 else{})
  norm=add(sq(X),sq(Y),scale(sq(AY),-1),c(-1))
  fail(norm==old[nr],f'actual principal norm {nr}')
  pairs.append((X,Y,AY,k));raw=add(raw,sq(add(X,c(-1))),sq(sub(Y,k)))
 raw=sub(raw,mul(v(131),v(198)))
 fail(sub(raw,add(*(old[i]for i in normrows)))==old[141],'complete source orientation identity')
 cap=add(sq(pairs[12][1]),scale(sq(nominal[12]),-1),c(-1),*(scale(sq(pairs[i][1]),-1)for i in range(14)if i!=12),scale(sq(v(201)),-1),scale(sq(v(202)),-1),scale(mul(v(203),add(v(203),c(1))),-1))
 fail(cap==old[144],'complete source cap identity')
 # Construct new rows from semantic formulas, not supplied edit coefficients.
 rs=copy.deepcopy(old)
 rs[91]=add(v(133),scale(v(130),4),scale(mul(v(130),v(132)),-8))
 rs[92]=add(v(134),scale(mul(v(130),v(133)),-4),scale(v(133),-1))
 rs[96]=add(v(138),sq(d),c(1),scale(mul(A,d),-2))
 X=add(c(1),scale(w,D));Y=scale(z,D);AY=scale(Z,D)
 rs[97]=add(F,scale(X,-1),AY,scale(mul(d,Y),-1),mul(v(138),v(139)))
 rs[126]=sub(Z,mul(A,z))
 rs[127]=add(scale(w,2),scale(sq(w),D),scale(sq(z),D),scale(sq(Z),-D))
 fail(scale(rs[127],D)==add(sq(X),sq(Y),scale(sq(AY),-1),c(-1)),'scaled norm division identity')
 rawnew={}
 for X0,Y0,AY0,k in pairs[:-1]:rawnew=add(rawnew,sq(add(X0,c(-1))),sq(sub(Y0,k)))
 rawnew=add(rawnew,sq(w),sq(sub(z,t)),scale(mul(v(131),v(198)),-1))
 rs[141]=sub(rawnew,add(*(old[i]for i in normrows[:-1])))
 # The cap has precisely the scaled z ordinate, not D*z.
 capnew=add(sq(pairs[12][1]),scale(sq(nominal[12]),-1),c(-1),*(scale(sq(pairs[i][1]),-1)for i in range(13)if i!=12),scale(sq(z),-1),scale(sq(v(201)),-1),scale(sq(v(202)),-1),scale(mul(v(203),add(v(203),c(1))),-1))
 fail(capnew==rs[144],'scaled cap literal identity')
 atoms=[('t',t),('t+1',add(t,c(1))),('F+t',add(F,t)),('x',v(1)),('growth_base',d),('B',v(3)),('F',F),('y+1',v(4)),('a',add(v(8),c(-1)))]
 atoms += [(name,v(i))for name,i in zip(['b','c','d','S','Sp','u','vq'],range(9,16))]
 atoms += [('C',scale(v(16),2)),('N',v(17)),('growth_index',scale(t,D)),('q',add(v(94),c(-1))),('q+1',v(94)),('BH',v(183))]
 atoms += [('pow'+str(k)+'.output',v(i))for k,i in [(3,95),(4,96),(5,100),(7,103),(8,106),(9,109),(10,112),(11,113),(12,116),(13,119),(14,120),(15,124),(16,127)]]
 requests=[(d,scale(t,D),F),(v(3),v(1),v(17)),(v(183),v(1),add(v(94),c(-1)))]
 requests += [(v(94),nominal[j],v(i))for j,i in [(1,95),(2,100),(3,103),(4,106),(5,109),(6,112),(8,116),(9,119),(11,124),(12,127)]]
 requests += [(add(v(94),c(-1)),nominal[j],v(i))for j,i in [(0,96),(7,113),(10,120)]]
 fail(len(requests)==16 and all(p in [a for _,a in atoms]for r in requests for p in r),'all 48 actual request ports framed')
 weights={}
 for _,a in atoms:
  fail(all(len(m)<=1 for m in a),'affine atom')
  fail(abs(a.get((),0))<=2,'atom constant')
  for m,b in a.items():
   if m:weights[m[0]]=max(weights.get(m[0],0),abs(b))
 rs[128]=add(v(130),c(-22),*(scale(sq(v(i)),-b)for i,b in weights.items()))
 fail(old[130]==add(t,c(-16),scale(sq(v(184)),-4)),'private deleted horizon')
 fail(all(184 not in m for i,p in enumerate(rs)if i!=130 for m in p),'private deleted coordinate')
 fail(56*22**2+56<4*22**3 and 88**4>D+1,'explicit orientation/frame thresholds')
 fail(2**23*(32+3)<2**32,'local precision threshold')
 return parent,rs,atoms,weights

def verify_bundle(bundle,inverse=True):
 parent,rs,atoms,weights=expected();cert=bundle['semantic'];base=bundle['base'];mapping=bundle['mapping'];eq=bundle['equation']
 fail(cert['source']=='sources/parent213.json'and cert['D']==D,'relative source and dyadic constant')
 fail(cert['source_sha256']==hashlib.sha256((ROOT/cert['source']).read_bytes()).hexdigest(),'semantic source hash')
 fail(cert['frame_constant']==22 and cert['frame_scale']==4 and cert['deleted_coordinate']==184 and cert['deleted_row']==130 and cert['cap_row']==144,'semantic frame/deletion parameters')
 fail(cert['growth_base']==terms(add(scale(var(0),4),const(2))) and cert['growth_index']==terms(scale(var(0),D)),'semantic growth parameters')
 fail(cert['scaled_coordinates']=={'w':180,'z':181,'Az':182},'scaled coordinate names')
 fail(base.get('inactive_rows')==[130] and base.get('inactive_coordinates')==[184],'staging inactive horizon')
 fail(cert['atoms']==[{'label':s,'terms':terms(a)}for s,a in atoms],'atom certificate')
 fail(cert['frame_weights']==[[i,c]for i,c in sorted(weights.items())],'weight certificate')
 expected_edits=[{'row':i,'old':parent['residuals'][i]['terms'],'new':terms(p)}for i,p in enumerate(rs)if p!=poly(parent['residuals'][i]['terms'])]
 fail(cert['edits']==expected_edits,'complete semantic edits')
 fail([poly(r['terms'])for r in base['residuals']]==rs,'complete semantic base')
 fail(cert['physical_pair']=={'X':terms(add(const(1),scale(var(180),D))),'Y':terms(scale(var(181),D))},'physical pair map')
 ops=read('operations.json');fail(mapping['operations']==ops,'operation certificate')
 fail(bundle['row_certificate']=={'input_sha256':hashlib.sha256(canon(base)).hexdigest(),'operations':ops,'output_sha256':hashlib.sha256(canon(eq)).hexdigest(),'omitted_private_coordinate':184,'omitted_private_row':130},'row certificate bindings')
 for number,op in enumerate(ops):
  before=copy.deepcopy(rs)
  if op['type']=='row':
   i,j,k=op['target'],op['source'],op['multiple'];fail(i!=j and type(k)is int and k!=0,'unit row operation')
   rs[i]=add(rs[i],scale(rs[j],k))
   if inverse:fail(sub(rs[i],scale(rs[j],k))==before[i],f'row inverse {number}')
  else:
   i=op['coordinate'];q=poly(op['image']);fail(q.get((i,))==1 and all(i not in m for m in q if m!=(i,)),'unit coordinate operation')
   rs=[substitute(p,i,q)for p in rs]
   inv=sub(scale(var(i),2),q)
   if inverse:fail([substitute(p,i,inv)for p in rs]==before,f'coordinate inverse {number}')
 keep=[i for i in range(213)if i!=184];ren={i:j for j,i in enumerate(keep)};rkeep=[i for i in range(152)if i!=130]
 fail(mapping['retained_old_coordinates']==keep and mapping['retained_old_rows']==rkeep,'deletion/renumbering maps')
 target=[{tuple(ren[j]for j in m):a for m,a in rs[i].items()}for i in rkeep]
 fail(eq['domain']=='unrestricted integers'and len(eq['variables'])==212,'unrestricted integer domain')
 fail([poly(r['terms'])for r in eq['residuals']]==target,'all output residual coefficients')
 fail(all(len(m)<=2 for p in target for m in p),'all rows quadratic')
 fail({i for p in target for m in p for i in m}==set(range(212)),'all coordinates live')
 met,pol=metric(eq,target)
 fail(bundle['metrics']==met,'all metrics')
 fail(bundle['expansion']=={'schema':'sparse_integer_polynomial_v1','variables':212,'terms':terms(pol)},'every collected coefficient')
 return {'status':'PASS','metrics':met,'actual_atoms':len(atoms),'underlying_frame_coordinates':len(weights),'actual_power_ports':48,'forward_inverse_operations':len(ops),'source_norms':14,'scaled_cap':True,'source_raw_orientation':True}

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
 lines=[s for s in (ROOT/'integer212/residuals.txt').read_text().splitlines()if re.match(r'^R[0-9]+ =',s)]
 fail(len(lines)==151,'text row count')
 for i,line in enumerate(lines):
  head,body=line.split('=',1);fail(head.strip()=='R'+str(i),'text row index');fail(parse_expression(body)==expected[i],'parsed text coefficient '+str(i))
 tex=(ROOT/'integer212/residuals.tex').read_text()
 blocks=re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}',tex,re.S)
 fail(len(blocks)==151,'TeX row count')
 for i,block in enumerate(blocks):
  head,body=block.split('=',1);fail(head.strip()=='R_{'+str(i)+'}','TeX row index')
  body=body.replace('&','').replace('{}','').replace('\\\\','')
  body=re.sub(r'x_\{([0-9]+)\}',r'x\1',body)
  body=re.sub(r'\^\{([0-9]+)\}',r'**\1',body)
  body=re.sub(r'(x[0-9]+(?:\*\*[0-9]+)?)(?=x)',r'\1*',body)
  body=re.sub(r'([0-9])\s+(?=x)',r'\1*',body)
  fail(parse_expression(body)==expected[i],'parsed TeX coefficient '+str(i))
 return {'plain_rows_parsed':151,'tex_rows_parsed':151}

def main():
 b={'semantic':read('semantic_certificate.json'),'base':read('base213/equation.json'),'mapping':read('coordinate_map.json'),'equation':read('integer212/equation.json'),'metrics':read('integer212/metrics.json'),'expansion':read('integer212/expanded_polynomial.json'),'row_certificate':read('row_certificate.json')}
 report=verify_bundle(b);report['printed_residuals']=check_prints(b['equation'])
 # Actual supplied-data corruptions, tested entirely in memory.
 mutations=[('semantic edit',lambda a:a['semantic']['edits'][0]['new'][0].__setitem__(0,777)),('atom',lambda a:a['semantic']['atoms'][0]['terms'][0].__setitem__(0,2)),('frame weight',lambda a:a['semantic']['frame_weights'][0].__setitem__(1,1)),('physical map',lambda a:a['semantic']['physical_pair']['Y'][0].__setitem__(0,D+1)),('base coefficient',lambda a:a['base']['residuals'][97]['terms'][0].__setitem__(0,999)),('coordinate map',lambda a:a['mapping']['retained_old_coordinates'].__setitem__(0,1)),('row map',lambda a:a['mapping']['retained_old_rows'].__setitem__(0,1)),('domain',lambda a:a['equation'].__setitem__('domain','natural numbers')),('final row',lambda a:a['equation']['residuals'][0]['terms'][0].__setitem__(0,999)),('quartic coefficient',lambda a:a['expansion']['terms'][0].__setitem__(0,999)),('metric',lambda a:a['metrics'].__setitem__('height',0)),('absolute path',lambda a:a['semantic'].__setitem__('source','/tmp/parent213.json')),('frame scale',lambda a:a['semantic'].__setitem__('frame_scale',1)),('inactive horizon',lambda a:a['base'].__setitem__('inactive_rows',[])),('row certificate hash',lambda a:a['row_certificate'].__setitem__('input_sha256','0'*64))]
 rejected=[]
 for name,mut in mutations:
  bad=copy.deepcopy(b);mut(bad)
  try:verify_bundle(bad,inverse=False)
  except (ValueError,KeyError,IndexError):rejected.append(name)
  else:raise ValueError('accepted corruption '+name)
 report['rejected_actual_corruptions']=rejected;report['optimized']=bool(sys.flags.optimize)
 print(json.dumps(report,sort_keys=True,indent=2))
if __name__=='__main__':main()
