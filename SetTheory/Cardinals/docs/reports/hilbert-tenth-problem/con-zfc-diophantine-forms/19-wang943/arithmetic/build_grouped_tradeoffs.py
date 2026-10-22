"""Owned bounded arithmetic constructor. Reads JSON data; never imports received code."""
import copy, hashlib, json, pathlib, random
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path(__file__).resolve().parent
PARENT=OUT/'upstream/start_only_ordinary69_system.json'
base=json.loads(PARENT.read_text())

def make_source(first,aux):
 d=copy.deepcopy(base)
 rows=[]
 for row in d['source']:
  out,op,a,b=row
  if first and out=='tau_square': continue
  if first and out=='first_next':
   rows.append(['restored_tau','+','first_root_base','tau_gap'])
   rows.append(['tau_square','*','restored_tau','restored_tau'])
  if aux and out=='aux_y2': continue
  if aux and out=='H2':
   rows.append(['restored_y','+','aux_u_rhs','aux_gap'])
   rows.append(['aux_y2','*','restored_y','restored_y'])
  rows.append(row)
 if first:d['witnesses'][d['witnesses'].index('tau_root')]='tau_gap'
 if aux:d['witnesses'][d['witnesses'].index('y_aux')]='aux_gap'
 d['source']=rows
 return d

def packet(name,first,aux,groups,degree):
 d=make_source(first,aux); rows=d['source']; residuals=[]
 for j,group in enumerate(groups):
  value=group[0]
  for k,v in enumerate(group[1:]):
   out=f'group{j}_product{k}'
   rows.append([out,'*',value,v]);value=out
  r=f'residual{j}'; rows.append([r,'-',value,1]);residuals.append(r)
 r='strong_residual';rows.append([r,'-','ordinary_I2','ordinary_Q']);residuals.append(r)
 squares=[]
 for j,r in enumerate(residuals):
  sq=f'square{j}';rows.append([sq,'*',r,r]);squares.append(sq)
 value=squares[0]
 for j,v in enumerate(squares[1:]):
  out=f'sum{j}';rows.append([out,'+',value,v]);value=out
 degrees={'norm_first':12 if first else 22,'norm_main':18,'norm_aux':22 if aux else 28,'norm_index':7,'norm_transport':2}
 d={k:d[k] for k in ['witnesses','fixed_numerals','source']}
 d.update(name=name,witness_domain='strictly positive integers',output=value,
  variable_count=15,exact_degree=degree,
  grouped_unit_factors=groups,residual_outputs=residuals,
  residual_exact_degrees=[sum(degrees[x] for x in g) for g in groups]+[22],
  positive_coordinate_changes=({'tau_root':'first_root_base+tau_gap'} if first else {})|({'y_aux':'aux_u_rhs+aux_gap'} if aux else {}),
  transport_coordinate='Original positive z_old, not the shifted system60 coordinate.',
  coefficient_binding='One coherent authentic four-port blank Start-only compiler tuple; MF is its shifted source port. Never mix ports from different compiler instances.',
  source_dependencies=['diophantine_zfc_round2/pell/start_only_ordinary69_system.json', '09-combined13 and 10-synthesis14 unit grouping; 12-gap-norm14 ordinary and auxiliary-gap proofs; prior15-release positive first gap proof'],
  parent_sha256=hashlib.sha256(PARENT.read_bytes()).hexdigest(),
  semantic_scope='Positive solvability equivalent to the ordinary Start-only system, by the attached proof and inherited compiler/Pell lemmas. Not an end-to-end proof-assistant certificate.')
 d['ledger']={'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)}
 (OUT/(name+'.json')).write_text(json.dumps(d,indent=2)+'\n')
 return d

def evaluate(d,env):
 env=dict(env)
 for out,op,a,b in d['source']:
  av=a if isinstance(a,int) else env[a];bv=b if isinstance(b,int) else env[b]
  env[out]=av+bv if op=='+' else av-bv if op=='-' else av*bv
 return env

def expected(d,e):
 J,F,alpha,z,f,h,i,T,s,w=e['Jrep'],e['F'],e['alpha'],e['transport_quotient'],e['f'],e['h'],e['i'],e['auxiliary_quotient'],e['s'],e['w']
 eta,zeta,gamma=e['eta'],e['zeta'],e['gamma']
 q=e['Bm1']*J+1; X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H
 L0=E*k*Y; tau=e['tau_root'] if 'tau_root' in e else L0+e['tau_gap']
 D=X+a*c+gamma*H;G=(q-1)*(q-F)+alpha;R=G*(q*q-1)+(e['MC']+q*e['MF'])*J
 V=c*(T*f-1)-R*f*f;y=e['y_aux'] if 'y_aux' in e else V+e['aux_gap']
 B=Delta*(f*f-1); I=i*c*c
 ns={'norm_first':tau*tau-L0*(L0+k),'norm_main':D*D-Delta*c*c,'norm_aux':B*(V*V-y*y)+y*y,
  'norm_index':k-h*E-R,'norm_transport':(e['Kconstant']+w)*(q-F-alpha)+(q-F)-z*(q-1)}
 vals=[]
 for group in d['grouped_unit_factors']:
  p=1
  for name in group:p*=ns[name]
  vals.append(p-1)
 vals.append(I*I-B)
 return sum(v*v for v in vals),vals

def audit(d):
 rows=d['source']; avail=set(d['witnesses']+d['fixed_numerals']);defs={}
 for out,op,a,b in rows:
  if out in avail or op not in ['+','-','*']:raise RuntimeError('Invalid DAG')
  if any(isinstance(x,str) and x not in avail for x in [a,b]):raise RuntimeError('Unbound operand')
  avail.add(out);defs[out]=[a,b]
 live={d['output']};todo=list(live)
 while todo:
  n=todo.pop()
  for a in defs.get(n,[]):
   if isinstance(a,str) and a not in live:live.add(a);todo.append(a)
 if live!=avail:raise RuntimeError('Dead gate or port: '+str(avail-live))
 rng=random.Random(20261022)
 for _ in range(100):
  e={v:rng.randrange(-3,5) for v in d['witnesses']+d['fixed_numerals']}
  got=evaluate(d,e);exp,rs=expected(d,e)
  if got[d['output']]!=exp or [got[x] for x in d['residual_outputs']]!=rs:raise RuntimeError('Formula mismatch')
 if d['exact_degree']!=2*max(d['residual_exact_degrees']):raise RuntimeError('Degree mismatch')
 return {'artifact':d['name']+'.json',**d['ledger'],'variables':len(d['witnesses']), 'residual_degrees':d['residual_exact_degrees'],'exact_degree':d['exact_degree'],'all_gates_and_ports_live':True,'independent_formula_cases':100}

if __name__=='__main__':
 cases=[('grouped_ordinary72_degree80',False,False,[['norm_first','norm_main'],['norm_aux','norm_index','norm_transport']],80),
 ('grouped_firstgap73_degree70',True,False,[['norm_first','norm_main','norm_transport'],['norm_aux','norm_index']],70),
 ('grouped_auxgap75_degree50',False,True,[['norm_first','norm_transport'],['norm_main','norm_index'],['norm_aux']],50),
 ('grouped_doublegap76_degree44',True,True,[['norm_first','norm_index'],['norm_main','norm_transport'],['norm_aux']],44)]
 result=[audit(packet(*case)) for case in cases]
 (OUT/'GROUPED_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
