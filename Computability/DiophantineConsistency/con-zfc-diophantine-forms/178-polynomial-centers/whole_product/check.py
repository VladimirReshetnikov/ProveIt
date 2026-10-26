#!/usr/bin/env python3
"""Independent exact check of the actual degree208 source graph.

Does not import build.py. Formal quotients are used only by this checker to
independently specify the intended integer polynomial center; the delivered
source graph has exclusively binary +,-,* instructions.
"""
from pathlib import Path
import json,hashlib,gzip,copy,collections,argparse,sys
sys.dont_write_bytecode=True
import exact_center as p
ROOT=Path(__file__).resolve().parent
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def arithmetic(op,x,y):
 if op=='+':return p.add(x,y)
 if op=='-':return p.add(x,p.scale(-1,y))
 if op=='*':return p.mul(x,y)
 raise ValueError('nonpolynomial operation')

def topology(e):
 inputs=e['witnesses']+e['fixed_numerals'];defined=set(inputs);parents={};weights={x:1 for x in e['witnesses']};weights.update({x:0 for x in e['fixed_numerals']})
 for name,op,x,y in e['source']:
  need(name not in defined,'duplicate source output')
  need(op in ['+','-','*'],'nonpolynomial source instruction')
  need(all(type(a) is int or a in defined for a in [x,y]),'undefined source input')
  parents[name]=[a for a in [x,y] if isinstance(a,str)];defined.add(name)
  dx=0 if type(x) is int else weights[x];dy=0 if type(y) is int else weights[y]
  weights[name]=dx+dy if op=='*' else max(dx,dy)
 live=set();todo=[e['output']]
 while todo:
  t=todo.pop()
  if t in live:continue
  live.add(t);todo+=parents.get(t,[])
 need(all(r[0] in live for r in e['source']),'dead paid instruction')
 need(all(i in live for i in inputs),'dead input')
 need(len(e['source'])==e['operations']==116,'wrong live operation count')
 need(dict(collections.Counter(r[1] for r in e['source']))==e['operation_breakdown'],'wrong operation breakdown')
 return weights

def preserved_source(e,parent):
 need(e['domain']==parent['domain']=='strictly positive integers','wrong domain')
 need(e['witnesses']==parent['witnesses'] and len(e['witnesses'])==10,'wrong quantified coordinates')
 need(e['fixed_numerals']==parent['fixed_numerals'],'wrong fixed coefficient ports')
 need(e['coefficient_binding']==parent['coefficient_binding'],'whole tuple changed')
 need(e['parent']['sha256']==sha((ROOT/'parent85.json').read_bytes()),'parent bytes changed')
 old={r[0]:r for r in parent['source']};new={r[0]:r for r in e['source']}
 for name,row in old.items():
  if name=='center':
   need(new['wp_raw_center']==['wp_raw_center',*row[1:]],'raw carrier changed')
   need(new['center']==['center','-','wp_raw_center','wp_W4'],'wrong whole center shift')
  elif name=='RG':need(new[name]==['RG','*','M2','wp_G16'],'wrong norm scaling target')
  else:need(new[name]==row,'parent instruction changed: '+name)
 need(new['wp_G16']==['wp_G16','*',16,'Dg'],'wrong norm scale')
 # Every extra row must be a center instruction or the two checked insertions.
 need(all(r[0] in old or r[0].startswith('wp_') for r in e['source']),'unreviewed extra instruction')

def actual_center(e):
 # A=Y(X+1)+1 implies XY=A-Y-1. Also ell+k=XY*kY+k.
 env={'Am1':p.add(p.A,p.C(-1)),'Y':p.Y,'kY':p.mul(p.k,p.Y),'U':p.U,'cTR':p.b,'c':p.c,'Dtau':p.E,'V':p.V,'k':p.k}
 xy=p.add(p.A,p.scale(-1,p.Y),p.C(-1))
 env['V0kk']=p.add(p.mul(xy,env['kY']),p.k)
 for name,op,x,y in e['source']:
  if name.startswith('wp_') and name not in ['wp_raw_center','wp_G16']:
   def get(a):return p.C(a) if type(a) is int else env[a]
   env[name]=arithmetic(op,get(x),get(y))
   if name=='wp_W4':break
 need('wp_W4' in env,'whole center not evaluated')
 Q1=p.quo(p.F,1);Q3=p.quo(p.F,3)
 need(all(c%2==0 for c in Q3.values()),'formal third quotient is not coefficientwise even')
 wanted=p.mul(p.U,p.add(p.scale(4,p.mul(p.A,p.F)),p.scale(-2,Q1),{m:-c//2 for m,c in Q3.items()}))
 need(env['wp_W4']==wanted,'actual center graph differs from independent formal-quotient polynomial')
 # This separately checks the quotient E identity used by the compact graph.
 need(env['wp_S']==p.quo(p.E,1),'actual S differs from quotient E')
 D=p.add(p.sq(env['wp_W4']),p.scale(-16,p.mul(p.G,p.sq(p.V))))
 expected_top={(8,8,8,6,2,0):8,(6,12,8,6,2,0):-48}
 need(p.weighted(D,p.weights)==106 and p.top(D,p.weights)==expected_top,'wrong exact norm cancellation or leading form')
 need(p.weighted(env['wp_W4'],p.weights)==65,'wrong center degree')
 return {'D':D,'W':env['wp_W4'],'top':expected_top}

def coefficient_tuple(e):
 out={};values={}
 for name,d in e['coefficient_binding']['ports'].items():
  raw=(ROOT/'coefficients'/d['file']).read_bytes();need(sha(raw)==d['gzip_sha256'],'compressed coefficient changed: '+name)
  uncompressed=gzip.decompress(raw);need(sha(uncompressed)==d['raw_sha256'],'coefficient bytes changed: '+name)
  v=int.from_bytes(uncompressed,'little');need(v.bit_length()==d['bits'],'coefficient bit length differs')
  values[name]=v;out[name]={'bytes':len(uncompressed),'bits':v.bit_length(),'raw_sha256':sha(uncompressed)}
 need(values['beta']>=31 and values['beta']%2==1 and values['K0']>0 and 0<values['MC']<values['beta']<values['MF']<2*values['beta'],'coefficient numerical bounds failed')
 return out

def run(e):
 parent=json.loads((ROOT/'parent85.json').read_text());preserved_source(e,parent);weights=topology(e);algebra=actual_center(e)
 # Independently propagate parent upper degrees. Its displayed leading forms
 # give exact Q80, M11, Z0<=21; only upper degree is needed for Z0.
 pw={x:1 for x in parent['witnesses']};pw.update({x:0 for x in parent['fixed_numerals']})
 for name,op,x,y in parent['source']:
  dx=0 if type(x) is int else pw[x];dy=0 if type(y) is int else pw[y];pw[name]=dx+dy if op=='*' else max(dx,dy)
 need({k:pw[k] for k in ['Q','Mtot','Znum','Dg','V']}=={'Q':80,'Mtot':11,'Znum':21,'Dg':50,'V':40},'parent cut degrees changed')
 # P=Q[Z0^2-2M Z0 W+M^2D]+16M^2G-(Z0-MW)^2.
 upper={'Q_Z0_squared':80+42,'Q_cross':80+11+21+65,'Q_M2_D':80+22+106,'scaled_norm_correction':22+50,'shifted_Z_squared':2*(11+65)}
 need(upper['Q_M2_D']==208 and all(v<208 for k,v in upper.items() if k!='Q_M2_D'),'leading-degree separation failed')
 need(e['exact_degree']==208,'metadata exact degree wrong')
 literal=json.loads((ROOT/'exact_polynomials.json').read_text())
 need(literal['variables']==p.names and literal['weights']==p.weights,'wrong literal coefficient order')
 need(literal['center']==p.serial(algebra['W']),'literal center coefficient array differs')
 need(literal['norm_defect']==p.serial(algebra['D']),'literal norm-defect coefficient array differs')
 need(literal['norm_defect_leading_terms']==p.serial(algebra['top']) and literal['norm_defect_weighted_degree']==106,'literal norm-defect leading certificate differs')
 return {'status':'PASS','operations':116,'operation_breakdown':e['operation_breakdown'],'center_monomials':len(algebra['W']),'norm_difference_monomials':len(algebra['D']),'norm_difference_degree':106,'norm_difference_leading_terms':p.serial(algebra['top']),'cut_order':p.names,'cut_weights':p.weights,'outer_degree_bounds':upper,'exact_total_degree':208,'coefficient_tuple':coefficient_tuple(e),'nonvanishing_argument':'At actual leading terms A=XY, U=i(kY)^2 and b=kYT-h^3(h-F), D106=8A^6Y^8k^8U^6b^2(A^2-6Y^4). Its two distinct w-powers cannot cancel; Q80=4A^6U^4E^2 and M11=24h^7A are nonzero. Thus the unique degree208 summand Q*M^2*D has nonzero leading form.','logical_scope':'Checks actual literal graph, all integer center coefficients, exact cancellation/degree and fixed numeral bytes. Unbounded positivity/Pell/native calibration is proved separately.'}

if __name__=='__main__':
 p0=argparse.ArgumentParser();p0.add_argument('--receipt',type=Path);args=p0.parse_args();eq=json.loads((ROOT/'equation.json').read_text());result=run(eq)
 controls=[]
 for target in ['wp_S','wp_Rc','wp_Sc','wp_W4','wp_G16']:
  bad=copy.deepcopy(eq);row=next(r for r in bad['source'] if r[0]==target);row[1]='+' if row[1]!='+' else '-'
  bad['operation_breakdown']=dict(collections.Counter(r[1] for r in bad['source']))
  try:run(bad)
  except (ValueError,KeyError) as ex:controls.append({'target':target,'rejected':True,'reason':str(ex)})
  else:raise ValueError('corrupted actual source accepted: '+target)
 result['corruption_controls']=controls
 if args.receipt:args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2))
