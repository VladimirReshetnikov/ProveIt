#!/usr/bin/env python3
"""Compose independent native guards and residue orientation; no external writes."""
from pathlib import Path
import json, hashlib
import sympy as s
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

def build():
    source=json.loads((ROOT/'upstream/residue/dependencies/quartic41.json').read_text())
    extra=['X3','J3','w3','tau_tail','cone1','cone2','cone3','cone_A','cone_B','Walpha','WC']
    sy={k:s.Symbol(k) for k in source['variables']+source['fixed_numerals']+extra}
    ps=lambda x:s.sympify(x,locals=sy)
    rs=list(map(ps,source['residuals']))
    private={f'{p}_pos{i}' for p in ('FA','FC') for i in range(1,4)}
    oldsquare=ps('X-2*u**2')
    removed=[i for i,e in enumerate(rs) if s.expand(e-oldsquare)==0 or e.free_symbols & {sy[x] for x in private}]
    need(len(removed)==3,'one old square row and two old guards')
    vs=[sy[x] for x in source['variables'] if x not in private and x!='u']+[sy[x] for x in ('cone1','cone2','cone3')]
    q=ps('beta*J+1');C=q-sy['F']-sy['alpha'];pos=ps('1+cone1**2+cone2**2+cone3*(cone3+1)')
    u=sy['cone_A']*sy['F'];v=sy['cone_B']*C
    xx=sy['beta']*sy['F']; yy=sy['Walpha']*sy['alpha']; zz=sy['WC']*C
    guards={'determinant':u*v-(q-u-v)**2-pos,'cone':2*(xx*yy+xx*zz+yy*zz)-xx**2-yy**2-zz**2-pos}
    metrics=[]
    def packet(name,rows,variables,ports,degree,witness,coefficient,restoration=None,parent=None):
        rows=[s.expand(e) for e in rows]
        need(len(variables)==len(set(variables)),name+' distinct variables')
        need(set.union(*(e.free_symbols for e in rows))==set(variables+ports),name+' exact live variable/port set')
        degrees=[s.Poly(e,*variables).total_degree() for e in rows]
        sos=s.Poly(s.expand(sum(e*e for e in rows)),*variables)
        need(sos.total_degree()==degree and max(degrees)*2==degree,name+' exact degree')
        need(sos.coeff_monomial(ps(witness))==coefficient,name+' source-independent nonzero leading coefficient')
        binding={'manifest':'COEFFICIENT_BINDING.json','path_base':'directory containing this polynomial JSON','ports':{str(p):'coefficients/'+str(p)+'.bin.gz' for p in ports},'backend':'mixed-parity-unrounded-1064921','MF_convention':'already shifted by beta'}
        out={'name':name,'domain':'unrestricted integers','variables':list(map(str,variables)),'variable_count':len(variables),'fixed_numerals':list(map(str,ports)),'residuals':list(map(str,rows)),'equation_count':len(rows),'residual_degrees':degrees,'exact_degree':degree,'single_polynomial':'sum of squares of the listed residuals','degree_witness':{'monomial':witness,'coefficient':coefficient},'coefficient_binding':binding,'repository_pin':'2605669a532342f153b13eb6b4a0af4b54f5fa37','proof_status':'Ordinary mathematical composition relative to explicitly inherited unbounded Pell/native/calibration theorems; finite algebra checks, not a new kernel proof.'}
        if restoration is not None:
            out['full_parent_restoration']={str(k):str(s.expand(v)) for k,v in restoration.items()}
            out['parent']=parent
        (ROOT/(name+'.json')).write_text(json.dumps(out,indent=2)+'\n')
        metric={'name':name,'variables':len(variables),'residuals':len(rows),'exact_degree':degree,'expanded_monomials_over_fixed_ports':len(sos.terms()),'degree_witness':out['degree_witness']}
        metrics.append(metric);print(json.dumps(metric))
    for kind,guard in guards.items():
        rows=[e for i,e in enumerate(rs) if i not in removed]+[guard]
        ports=[sy[x] for x in source['fixed_numerals']+(['cone_A','cone_B'] if kind=='determinant' else ['Walpha','WC'])]
        # Direct orientation is preferable for the quartic expansion.
        sub={sy['X']:3*sy['X3']-1}
        drows=[s.expand(e.subs(sub,simultaneous=True)) for e in rows]
        dvs=[sy['X3'] if x==sy['X'] else x for x in vs]
        packet(kind+'37_quartic_direct',drows,dvs,ports,4,'tau**4',1)
        # This congruence slice preserves monic X, so enables smaller companions.
        sub={sy['J']:3*sy['J3']+1,sy['w_scale']:3*sy['w3']+1}
        arows=[s.expand(e.subs(sub,simultaneous=True)) for e in rows]
        avs=[sy['J3'] if x==sy['J'] else sy['w3'] if x==sy['w_scale'] else x for x in vs]
        aname=kind+'37_quartic_affine'
        packet(aname,arows,avs,ports,4,'tau**4',1)
        q=ps('beta*(3*J3+1)+1');W=ps('4*(3*w3+1)')
        restoration={sy['P']:ps('eta+zeta+E*(c-eta)'),sy['N']:q*(sy['L']+1),sy['X']:q*W,sy['C2']:ps('c**2'),sy['F2']:ps('f**2'),sy['g']:ps('y**2-V**2'),sy['tau']:ps('tau_tail+E*(c-eta)')}
        rr=[s.expand(e.subs(restoration,simultaneous=True)) for e in arows];rr=[e for e in rr if e!=0]
        vv=[sy['tau_tail'] if x==sy['tau'] else x for x in avs if x not in restoration or x==sy['tau']]
        need(len(rr)==18 and len(vv)==31,'sextic dimensions')
        packet(kind+'31_sextic',rr,vv,ports,6,'r**2*c**4',4,restoration,aname+'.json')
        k=ps('1-V+j*c+h*E')
        restoration={sy['L']:q*q-1,sy['N']:q**3,sy['X']:q*W,sy['C2']:ps('c**2'),sy['F2']:ps('f**2'),sy['g']:ps('y**2-V**2'),sy['Baux']:ps('I**2'),sy['D']:q*W+ps('a*c+gamma*(4*a+3)'),sy['Delta']:ps('a**2+4*a+3'),sy['zeta']:k-sy['eta'],sy['P']:k+ps('E*(c-eta)')}
        rr=[s.expand(e.subs(restoration,simultaneous=True)) for e in arows];rr=[e for e in rr if e!=0]
        vv=[x for x in avs if x not in restoration]
        need(len(rr)==13 and len(vv)==26,'octic dimensions')
        packet(kind+'26_octic',rr,vv,ports,8,'a**4*f**4',1,restoration,aname+'.json')
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
if __name__=='__main__':build()
