#!/usr/bin/env python3
"""New generators. Received sources are inert JSON, never imported or executed."""
import copy, hashlib, json
from collections import Counter
from pathlib import Path
H=Path(__file__).resolve().parent
FIXED=['beta','K0','MC','MF']
GUARDED=['J','F','alpha','z','eta','zeta']
BIND={'manifest':'../coefficients/COMPACT_COEFFICIENT_BINDING.json','tuple':'complete source19/source30 compact Wang943, B=2^(5^10)','port_map':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'warning':'All four fixed ports are one tuple; MF_source is already shifted. Historical source bindings do not select these new artifacts.'}
def read(p):return json.loads((H/p).read_text())
def save(p):
    p['coefficient_binding']=BIND;p['proof']='PROOF.md';p['formal_status']='Ordinary mathematical reduction plus finite arithmetic audits, not an end-to-end proof-assistant certificate.'
    names=set(p['variables']+FIXED);live=set([p['output']] if 'output'in p else [x for a in p['comparisons'] for x in a if isinstance(x,str)])
    for n,op,a,b in p['source']:
        assert n not in names and op in ['+','-','*'];assert all(isinstance(x,int) or x in names for x in [a,b]);names.add(n)
    for n,op,a,b in reversed(p['source']):
        if n in live:live.update(x for x in [a,b] if isinstance(x,str))
    assert names<=live, names-live
    count=Counter(x[1] for x in p['source']);p['ledger']={'operations':len(p['source']),'multiplications':count['*'],'additions_subtractions':count['+']+count['-'],'all_gates_live':True,'all_inputs_live':True}
    p['variable_count']=len(p['variables']);p['fixed_numerals']=FIXED;p['domain']='unrestricted integers'
    (H/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    return {k:p[k] for k in ['name','variable_count','equation_count','exact_degree','ledger']}
def prefix(retained=False):
    rows=[];vs=[];guards=[]
    for x in GUARDED:
        a,b,c=[x+'_pos'+str(j) for j in [1,2,3]];vs += [a,b,c]
        p='pos_'+x
        rows += [[p+'a','*',a,a],[p+'b','*',b,b],[p+'cp1','+',c,1],[p+'c','*',c,p+'cp1'],[p+'ab','+',p+'a',p+'b'],[p+'abc','+',p+'ab',p+'c'],[p if retained else x,'+',p+'abc',1]]
        if retained:guards.append([x,p])
    return rows,vs,guards
def make_quartic():
    old=read('upstream/arithmetic/quartic31_system.json');old51=read('upstream/source27/integer51_degree4.json')
    rows=[['odd_i_twice','*',2,'r'],['i','+','odd_i_twice',1],['odd_s_twice','*',2,'s_odd'],['s','+','odd_s_twice',1]]
    for row in old['source']:
        if row[0]=='g51':continue
        if row[0]=='g53':row=['g53','+','F','g52']
        rows.append(row)
    comps=[(['g50','g53'] if a==['g53',1] else a) for a in old['comparisons']]
    rows.append(['square_w','*','u','u']);comps.append(['w','square_w'])
    added,_,guards=prefix(True);rows+=added;comps+=guards
    p={'name':'integer50_quartic_system','variables':[x for x in old51['variables'] if x!='G'],'source':rows,'comparisons':comps,'equation_count':29,'exact_degree':2,'sos_degree':4,'transformation':'G packing elimination over integers; i=2r+1, s=2s_odd+1, w=u^2; six retained positive registers guarded by Pos. Transport z is shifted.'}
    results=[save(p)];p=copy.deepcopy(p);p['name']='integer50_quartic';p['exact_degree']=4;p['equation_count']=1;p['degree_certificate']={'monomial':'tau^4','coefficient':1}
    squares=[]
    for j,(a,b) in enumerate(p.pop('comparisons')):
        r='res_'+str(j);sq='square_'+str(j);p['source'] += [[r,'-',a,b],[sq,'*',r,r]];squares.append(sq)
    out=squares[0]
    for j,sq in enumerate(squares[1:]):
        n='sum_'+str(j);p['source'].append([n,'+',out,sq]);out=n
    p['output']=out;results.append(save(p));return results
def make_ratio():
    old=read('upstream/positive/positive12_product.json');rows,vs,_=prefix(False)
    rows += [['odd_i_twice','*',2,'i_integer'],['i','+','odd_i_twice',1],['odd_s_twice','*',2,'s_integer'],['s','+','odd_s_twice',1],['w','*','w_integer','w_integer']]
    vs += ['i_integer','s_integer','w_integer','h','T','t']
    for row in old['source']:
        n=row[0]
        if n=='P':
            rows += [['H2','*','H','H'],['HQ','*','H2','Q']];continue
        if n in ['U','H2']:continue
        if n=='HP':row=['HP','*','HQ','g53']
        if n=='HU':row=['HU','*','HQ','g55']
        if n=='g57':continue
        if n=='M':
            rows += [['ratio_iI','*','i','I'],['ratio_Rac','*','R','g23'],['ratio_product','*','ratio_iI','ratio_Rac'],['ratio_five','*',5,'ratio_product'],['ratio_sum','+','ratio_five','v2'],['M','*',2,'ratio_sum']]
            continue
        if n=='g64':rows.append(['first_weight','*',2,'HM']);row=['g64','*','first_weight','first_weight']
        if n in ['g101','g102','g103']:continue
        if n=='g104':
            rows += [['trace_vbar','*','Trace','vbar'],['ur_trace_vbar','-','ur','trace_vbar'],['g104','*','ur','ur_trace_vbar']];continue
        if n=='vr':row=['vbar','-','coef','g95']
        if n=='g105':row=['g105','*','vbar','vbar']
        rows.append(row)
    p={'name':'integer24_ratio_product','variables':vs,'source':rows,'output':'polynomial','equation_count':1,'exact_degree':1936,'norm_degree':1920,'weight':'M=2*(5*R*a*c*i*I+v^2), L=1+H*M, first-root weight 2*H*M','norm':'Product over u^2=G, tau^2=A and f^2=D of d*(S-L*u-2*H*M*tau)^2-H^2*e+H^2*Baux*f','degree_certificate':'N_top=(99*899)^4*d_top^8*H_top^16*b_top^16; multiply Nk_top Nt_top.'}
    results=[save(p)];q=copy.deepcopy(p);q.pop('output');q['source']=q['source'][:-5]
    for row in q['source']:
        if row[0]=='ur_trace_vbar':row[:]=['ur_trace_vbar','-','trace_vbar','ur']
    q['comparisons']=[['Nk',1],['Nt',1],['g104','g106']];q['comparison_note']='Third comparison is -N=0 after moving the Knorm*vbar^2 term to the other side; no gate computes N.';q['name']='integer24_ratio_system';q['equation_count']=3;q['exact_degree']=1920;results.append(save(q))
    q=copy.deepcopy(p);q['source']=q['source'][:-4];q['name']='integer24_ratio_sos';q['source'] += [['rk','-','Nk',1],['rt','-','Nt',1],['rk2','*','rk','rk'],['rt2','*','rt','rt'],['N2','*','N','N'],['sos01','+','rk2','rt2'],['sos','+','sos01','N2']];q['output']='sos';q['equation_count']=1;q['exact_degree']=3840;results.append(save(q));return results
def main():
    results=make_quartic()+make_ratio();(H/'BUILD_RESULTS.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
