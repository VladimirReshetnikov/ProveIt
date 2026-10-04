#!/usr/bin/env python3
"""Recovered edition: newly authored reconstruction retained from pre-reset context.
No upstream program, module, or saved arithmetic schedule is executed or imported.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import sympy as sp
HERE=Path(__file__).resolve().parent
PARAMETERS = ['InitialMemoryPlus','FinalMemoryPlus','InitialHead','FinalHead','FinalSignPlus']
RAW = ['A','B','GE','GW','GN','GS','D','E','F','G','Z','SW','SN']
GEOMETRY = ['q','Q','W','uQ','uW','Gt','Gy','WidthOdd','HeightEven','K','Wp','HeadRoot','HeadQuot']
FIELDS = ['A','B','C','D','E','F','G','GE','GW','GN','GS','TestE','TestW','TestN','TestS']
PELL = ['a','c','d','f','h','i','j','k','o','r','s','w','tau','eta','zeta','ga','y_aux']
WITNESSES = [x+'Plus' for x in RAW]+GEOMETRY+['Bound'+x for x in FIELDS+['Z']]+['BoundInitial','BoundHead']+PELL

def need(p, why):
    if not p: raise ValueError(why)

def construct():
    nodes=[]; tests=[]; groups=Counter(); equation_labels=[]
    def n(out,kind,left,right,group):
        nodes.append([out,kind,left,right]);groups[group]+=1;return out
    def eq(label,left,right):
        tests.append([left,right]);equation_labels.append(label)
    for x in RAW: n(x,'-',x+'Plus',1,'positive adapters')
    for out,p in [('I','InitialMemoryPlus'),('FM','FinalMemoryPlus'),('FZ','FinalSignPlus')]:
        n(out,'-',p,1,'positive adapters')
    g='extent geometry'
    n('q_extent','*','Q','uQ',g);eq('q extent','q','q_extent')
    n('Q_extent','*','W','uW',g);eq('Q extent','Q','Q_extent')
    for x in ['q','Q','W']: n(x+'_minus_one','-',x,1,g)
    n('time_sum','*','Gt','Q_minus_one',g);eq('time repunit','q_minus_one','time_sum')
    n('row_sum','*','Gy','W_minus_one',g);eq('row repunit','Q_minus_one','row_sum')
    g='checkerboard geometry'
    n('oddwidth8','*',8,'WidthOdd',g);n('oddwidth_rhs','+','oddwidth8',3,g);eq('odd width','W','oddwidth_rhs')
    n('W_plus_one','+','W',1,g);n('evenheight_rhs','*','W_plus_one','HeightEven',g);eq('even height','Gy','evenheight_rhs')
    n('K_eight','*',8,'K',g);eq('checkerboard mask','q_minus_one','K_eight')
    n('Odd','*',3,'K',g)
    n('Wp_three','*',3,'Wp',g);eq('last-column power','W','Wp_three')
    n('VH','*','Gt','HeightEven',g);n('Eedge','*','Wp','VH',g)
    n('Nedge','*','Gt','WidthOdd',g);n('Sbase3','*',3,'Nedge',g)
    n('Sbase','+','Sbase3','Gt',g);n('Sedge','*','uW','Sbase',g)
    for direction,wrong,edge in [('E','Odd','Eedge'),('W','Odd','VH'),('N','K','Nedge'),('S','K','Sedge')]:
        n('Forbidden'+direction,'+',wrong,edge,g)
        n('Test'+direction,'+','G'+direction,'Forbidden'+direction,'edge tests')
    g='initial interface'
    n('initial_range','+','I','BoundInitial',g);eq('initial word bound','initial_range','Q')
    n('head_range','+','InitialHead','BoundHead',g);eq('initial head bound','head_range','Q')
    n('head_divisor','*','InitialHead','HeadQuot',g);eq('initial head power','q','head_divisor')
    n('head_square','*','HeadRoot','HeadRoot',g);eq('initial head parity','InitialHead','head_square')
    g='local and head sums'
    n('Ce','+','GE','GW',g);n('Co','+','GN','GS',g);n('C','+','Ce','Co',g);n('Zprime','+','GW','GN',g)
    n('DE','+','D','E',g);eq('active partition','C','DE')
    n('AE','+','A','E',g);n('BD','+','B','D',g);eq('memory toggle','AE','BD')
    n('FG','+','F','G',g);eq('visited-color partition','D','FG')
    n('ZG','+','Z','G',g);n('ZprimeF','+','Zprime','F',g);eq('heading toggle','ZG','ZprimeF')
    n('SE','*',3,'GE','spatial shifts');n('SW_three','*',3,'SW','spatial shifts');eq('west shift','SW_three','GW')
    n('SS','*','W','GS','spatial shifts');n('SN_W','*','W','SN','spatial shifts');eq('north shift','SN_W','GN')
    n('NextEW','+','SE','SW',g);n('NextNS','+','SN','SS',g)
    n('NextC','+','NextEW','NextNS',g);n('NextZ','+','SW','SS',g)
    g='head time wiring'
    n('q_FinalHead','*','q','FinalHead',g);n('Q_NextC','*','Q','NextC',g)
    n('head_time_left','+','C','q_FinalHead',g);n('head_time_right','+','InitialHead','Q_NextC',g);eq('head recurrence','head_time_left','head_time_right')
    n('q_FZ','*','q','FZ',g);n('Q_NextZ','*','Q','NextZ',g)
    n('sign_time_left','+','Z','q_FZ',g);eq('sign recurrence','sign_time_left','Q_NextZ')
    g='memory time wiring'
    n('q_FM','*','q','FM',g);n('Q_B','*','Q','B',g)
    n('memory_time_left','+','A','q_FM',g);n('memory_time_right','+','I','Q_B',g);eq('memory recurrence','memory_time_left','memory_time_right')
    for x in FIELDS+['Z']:
        n('bound_'+x,'+',x,'Bound'+x,'field bounds');eq(x+' strict bound','bound_'+x,'q')
    packed='D'
    for ix,x in enumerate(reversed(FIELDS)):
        mul=n('pack_product_'+str(ix),'*','q',packed,'packing')
        packed=n('pack_sum_'+str(ix),'+',x,mul,'packing')
    g='mask and Pell'
    for name,l,r in [('q2','q','q'),('q4','q2','q2'),('q8','q4','q4'),('L','q8','q8')]:n(name,'*',l,r,g)
    n('D0','*',9,'L',g);n('three_P','*',3,packed,g);n('mask_gap','-','D0','three_P',g);n('mask_r','-','mask_gap',1,g)
    eq('mask index','r','mask_r')
    # Own reconstruction of the proof's 43-operation Pell block.
    n('pell_U','*','w','D0',g);n('pell_Y','*','s','D0',g);n('pell_E','*','pell_U','pell_Y',g)
    n('pell_a_rhs','+','pell_E','pell_Y',g)
    n('pell_Yk','*','pell_Y','k',g);n('pell_E2','*','pell_E','pell_E',g)
    n('pell_first_coefficient','+','pell_E2','pell_U',g);n('pell_Yk2','*','pell_Yk','pell_Yk',g)
    n('pell_first_left','*','pell_first_coefficient','pell_Yk2',g)
    n('tau_plus_one','+','tau',1,g);n('pell_first_right','*','tau','tau_plus_one',g)
    n('interval_c_rhs','+','pell_Yk','eta',g);n('interval_k_rhs','+','eta','zeta',g)
    n('r_plus_one','+','r',1,g);n('pell_hE','*','h','pell_E',g)
    n('pell_k_rhs','+','r_plus_one','pell_hE',g);n('pell_J','+','r_plus_one','r',g)
    n('pell_ac','*','a','c',g);n('pell_U_ac','+','pell_U','pell_ac',g)
    n('pell_six_a','*',6,'a',g);n('pell_M','+','pell_six_a',8,g)
    n('pell_gaM','*','ga','pell_M',g);n('pell_d_rhs','+','pell_U_ac','pell_gaM',g)
    n('pell_a2','*','a','a',g);n('pell_Delta','+','pell_a2','pell_M',g)
    n('pell_c2','*','c','c',g);n('pell_Dc2','*','pell_Delta','pell_c2',g)
    n('pell_main_right','+','pell_Dc2',1,g);n('pell_main_left','*','d','d',g)
    n('pell_R','*','i','pell_c2',g);n('pell_R2','*','pell_R','pell_R',g)
    n('pell_f2','*','f','f',g);n('pell_f2m1','-','pell_f2',1,g);n('pell_relaxed_right','*','pell_Delta','pell_f2m1',g)
    n('pell_of','*','o','f',g);n('pell_u_rhs','+','c','pell_of',g)
    n('pell_jc','*','j','c',g);n('pell_u','+','pell_J','pell_jc',g)
    n('pell_u2','*','pell_u','pell_u',g);n('pell_y2','*','y_aux','y_aux',g)
    n('pell_difference','-','pell_u2','pell_y2',g)
    n('pell_half_left','*','pell_R2','pell_difference',g);n('pell_half_right','-',1,'pell_y2',g)
    for label,l,r in [('first Pell norm','pell_first_left','pell_first_right'),('ratio lower slack','c','interval_c_rhs'),('ratio upper slack','k','interval_k_rhs'),('first Pell index','k','pell_k_rhs'),('Pell coefficient','a','pell_a_rhs'),('power-three congruence','d','pell_d_rhs'),('main Pell norm','pell_main_left','pell_main_right'),('relaxed auxiliary norm','pell_R2','pell_relaxed_right'),('half-parameter norm','pell_half_left','pell_half_right'),('auxiliary congruence','pell_u','pell_u_rhs')]:eq(label,l,r)
    return dict(schema='arithmetic-dag-v1',parameters=PARAMETERS,witnesses=WITNESSES,
                input_domain='all parameters and witnesses are strictly positive integers; arithmetic nodes range over all integers',
                nodes=nodes,equalities=tests,equation_labels=equation_labels,groups=dict(groups),
                exports={'W':'W','Wp':'Wp','Q':'Q','q':'q','I':'I','FM':'FM','FZ':'FZ','P':packed,'D0':'D0'},
                fixed_numerals=sorted({v for row in nodes for v in row[2:] if type(v) is int}))

def source_polynomials(symbols):
    # Independently stated residuals in supplied inputs only, no DAG traversal.
    z=symbols
    raw={x:z[x+'Plus']-1 for x in RAW}
    q,Q,W,Gt,Gy,K,Wp=[z[x] for x in ['q','Q','W','Gt','Gy','K','Wp']]
    I,FM,FZ=[z[x]-1 for x in ['InitialMemoryPlus','FinalMemoryPlus','FinalSignPlus']]
    C=raw['GE']+raw['GW']+raw['GN']+raw['GS'];Zp=raw['GW']+raw['GN']
    NC=3*raw['GE']+raw['SW']+raw['SN']+W*raw['GS'];NZ=raw['SW']+W*raw['GS']
    forbidden={'E':3*K+Wp*Gt*z['HeightEven'],'W':3*K+Gt*z['HeightEven'],
               'N':K+Gt*z['WidthOdd'],'S':K+z['uW']*(3*Gt*z['WidthOdd']+Gt)}
    values=dict(raw,C=C,**{'Test'+d:raw['G'+d]+forbidden[d] for d in 'EWNS'})
    residuals=[q-Q*z['uQ'],Q-W*z['uW'],q-1-Gt*(Q-1),Q-1-Gy*(W-1),
               W-8*z['WidthOdd']-3,Gy-(W+1)*z['HeightEven'],q-1-8*K,W-3*Wp,
               I+z['BoundInitial']-Q,z['InitialHead']+z['BoundHead']-Q,q-z['InitialHead']*z['HeadQuot'],z['InitialHead']-z['HeadRoot']**2,
               C-raw['D']-raw['E'],raw['A']+raw['E']-raw['B']-raw['D'],raw['D']-raw['F']-raw['G'],raw['Z']+raw['G']-Zp-raw['F'],
               3*raw['SW']-raw['GW'],W*raw['SN']-raw['GN'],
               C+q*z['FinalHead']-z['InitialHead']-Q*NC,raw['Z']+q*FZ-Q*NZ,raw['A']+q*FM-I-Q*raw['B']]
    residuals.extend(values[x]+z['Bound'+x]-q for x in FIELDS+['Z'])
    P=sum(values[x]*q**k for k,x in enumerate(FIELDS+['D']))
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[x] for x in PELL]
    D0=9*q**16;U=w*D0;Y=s*D0;Qpell=U*Y**2;Delta=(a+3)**2-1;u=2*r+1+j*c
    residuals.extend([r-D0+3*P+1,Qpell*(Qpell+1)*k*k-tau*(tau+1),c-Y*k-eta,k-eta-zeta,
                      k-r-1-h*U*Y,a-Y*(U+1),d-U-a*c-ga*(6*a+8),d*d-Delta*c*c-1,
                      (i*c*c)**2-Delta*(f*f-1),Delta*(f*f-1)*(u*u-y*y)-(1-y*y),u-c-o*f])
    return [sp.expand(x) for x in residuals]

def check(data):
    need(data['parameters']==PARAMETERS and data['witnesses']==WITNESSES,'changed quantified interface')
    need(data['fixed_numerals']==sorted({v for row in data['nodes'] for v in row[2:] if type(v) is int}),'changed numeral declaration')
    inputs=data['parameters']+data['witnesses'];need(len(inputs)==len(set(inputs)),'duplicate input')
    z={x:sp.Symbol(x) for x in inputs};env=dict(z);count=Counter()
    for out,kind,l,r in data['nodes']:
        need(out not in env,'register redefinition '+out);need(kind in ['+','-','*'],'unknown operation')
        def read(v):
            need(type(v) is int or type(v) is str,'nonliteral operand')
            if type(v) is int:return sp.Integer(v)
            need(v in env,'undeclared/forward operand '+v);return env[v]
        left,right=read(l),read(r)
        env[out]={'+':lambda:left+right,'-':lambda:left-right,'*':lambda:left*right}[kind]()
        count[kind]+=1
    source=source_polynomials(z);records=[];correction=source[-3]*((2*z['r']+1+z['j']*z['c'])**2-z['y_aux']**2)
    degrees=[]
    for index,((l,r),expected) in enumerate(zip(data['equalities'],source,strict=True)):
        need(l in env and r in env,'unknown equality register')
        actual=sp.expand(env[l]-env[r]);adjustment=correction if index==len(source)-2 else sp.Integer(0)
        need(sp.expand(actual-expected-adjustment)==0,'polynomial mismatch '+str(index))
        poly=sp.Poly(actual,*z.values());degree=int(poly.total_degree());degrees.append(degree)
        records.append(dict(index=index,label=data['equation_labels'][index],equality=[l,r],source=str(expected),actual=str(actual),degree=degree,correction=str(sp.expand(adjustment))))
    need(len(data['nodes'])==174,'operation total');need(count['*']==72 and count['+']+count['-']==102,'histogram')
    need(len(data['equalities'])==48 and len(data['witnesses'])==61,'interface size')
    need(sum(data['groups'].values())==174,'group total')
    need(set(inputs)<=set(v for row in data['nodes'] for v in row[2:] if isinstance(v,str))|set(v for e in data['equalities'] for v in e),'unused input')
    maxdeg=max(degrees);maxids=[i for i,d in enumerate(degrees) if d==maxdeg]
    leading=[]
    for i in maxids:
        p=sp.Poly(records[i]['actual'],*z.values())
        terms=[{'coefficient':int(coeff),'powers':{name:power for name,power in zip(inputs,powers) if power}} for powers,coeff in p.terms() if sum(powers)==maxdeg]
        leading.append(dict(index=i,terms=terms))
    return dict(status='PASS',operations=174,multiplications=count['*'],additions=count['+'],subtractions=count['-'],additions_subtractions=count['+']+count['-'],equations=48,positive_parameters=5,positive_witnesses=61,fixed_numerals=data['fixed_numerals'],groups=data['groups'],maximum_actual_residual_degree=maxdeg,maximum_actual_residual_indices=maxids,leading_homogeneous_certificate=leading,sum_of_squares_degree=2*maxdeg,residuals=records,proof_scope='Exact formal integer-polynomial identity, literal DAG acyclicity and counts. General positive-domain equivalence inherited from pinned theorem; no execution/import of upstream code or schedules.')

def main():
    data=construct();receipt=check(data)
    for filename,obj in [('history174.json',data),('verification.json',receipt)]:
        (HERE/filename).write_text(json.dumps(obj,indent=2)+'\n')
    digest=hashlib.sha256((HERE/'history174.json').read_bytes()).hexdigest()
    need(digest=='2075bb290f3f81d7c04a27b82f50c4f492638d55a3a27f434f66497ae9fb90ea','retained byte identity mismatch')
    print(json.dumps({k:v for k,v in receipt.items() if k!='residuals'},indent=2));print('EXACT RECOVERED history174.json SHA256',digest)
if __name__=='__main__':main()
