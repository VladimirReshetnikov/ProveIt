#!/usr/bin/env python3
"""Build exact joint-guard packets. Source JSON is parsed as inert arithmetic."""
from pathlib import Path
import ast, hashlib, json
import sympy as s

ROOT=Path(__file__).resolve().parent

def need(ok, message):
    if not ok: raise ValueError(message)

def main():
    raw=(ROOT/'upstream/determinant26_octic.json').read_bytes()
    src=json.loads(raw)
    pin=json.loads((ROOT/'SOURCE_PIN.json').read_text())
    need(hashlib.sha256(raw).hexdigest()==pin['sha256'], 'source identity')
    extra=['pair_root','pair_pos1','pair_pos2','pair_pos3','zeta']
    sy={n:s.Symbol(n) for n in src['variables']+src['fixed_numerals']+extra}
    def parse(text):
        def walk(n):
            if isinstance(n,ast.Expression):return walk(n.body)
            if isinstance(n,ast.Name) and n.id in sy:return sy[n.id]
            if isinstance(n,ast.Constant) and type(n.value)==int:return s.Integer(n.value)
            if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -walk(n.operand)
            if isinstance(n,ast.BinOp):
                a,b=walk(n.left),walk(n.right)
                if isinstance(n.op,ast.Add):return a+b
                if isinstance(n.op,ast.Sub):return a-b
                if isinstance(n.op,ast.Mult):return a*b
                if isinstance(n.op,ast.Pow) and b.is_Integer and 0<=b<=16:return a**b
            raise ValueError(ast.dump(n))
        return walk(ast.parse(text,mode='eval'))
    pos=lambda a,b,c:1+a*a+b*b+c*(c+1)
    q=parse('beta*(3*J3+1)+1')
    U=parse('cone_A*F'); W=sy['cone_B']*(q-sy['F']-sy['alpha'])
    d=U*W-(q-U-W)**2
    z0=parse('1-V+j*c+h*E-eta')
    y0=sy['eta']*z0
    need(s.expand(parse(src['residuals'][-2])-y0+parse('1+eta_zeta_pos1**2+eta_zeta_pos2**2+eta_zeta_pos3*(eta_zeta_pos3+1)'))==0,'old common-sign guard')
    need(s.expand(parse(src['residuals'][-1])-d+parse('1+cone1**2+cone2**2+cone3*(cone3+1)'))==0,'old determinant guard')
    base=[n for n in src['variables'] if not n.startswith(('eta_zeta_pos','cone'))]
    new_names=['pair_root','pair_pos1','pair_pos2','pair_pos3']
    t=sy['pair_root']; positive=pos(*(sy[n] for n in new_names[1:]))
    results=[]
    for retain in [False,True]:
        nvars=base+(['zeta'] if retain else [])+new_names
        y=sy['eta']*sy['zeta'] if retain else y0
        guard=s.expand(d*y-(t*t-d-y+1)**2-positive)
        rows=src['residuals'][:-2]+([str(s.expand(sy['zeta']-z0))] if retain else [])+[str(guard)]
        name='joint25_octic' if retain else 'joint24_degree12'
        vr=[sy[n] for n in nvars]
        rr=[parse(e) for e in rows]
        pp=[s.Poly(e,*vr) for e in rr]
        degree=8 if retain else 12
        witness=t**8 if retain else parse('eta**4*h**4*E**4')
        sos=s.Poly(sum(e*e for e in rr),*vr)
        need(len(nvars)==(25 if retain else 24),'variable count')
        need(len(rr)==(13 if retain else 12),'residual count')
        need(max(p.total_degree() for p in pp)==degree//2 and sos.total_degree()==degree,'degree')
        need(sos.coeff_monomial(witness)==1,'degree certificate')
        need(set().union(*(e.free_symbols for e in rr))==set(vr+[sy[n] for n in src['fixed_numerals']]),'all and only declared symbols')
        if retain:
            need(s.expand(guard.subs(sy['zeta'],z0)-(d*y0-(t*t-d-y0+1)**2-positive))==0,'projection identity')
        packet={
            'name':name,'domain':'unrestricted integers','variables':nvars,'variable_count':len(nvars),
            'fixed_numerals':src['fixed_numerals'],'residuals':rows,'residual_count':len(rr),
            'residual_degrees':[p.total_degree() for p in pp],
            'single_equation':'sum of squares of all residuals','exact_degree':degree,
            'degree_witness':{'monomial':str(witness),'coefficient':1},
            'parent':'upstream/determinant26_octic.json','parent_sha256':pin['sha256'],
            'coefficient_binding':{'manifest':'../guards/COEFFICIENT_BINDING.json','ports':{n:'../guards/'+v for n,v in src['coefficient_binding']['ports'].items()},'backend':src['coefficient_binding']['backend'],'MF_convention':src['coefficient_binding']['MF_convention']},
            'proof':'PROOF.md','proof_status':src['proof_status'],
            'guard_registers':{'q':str(q),'U':str(U),'W':str(W),'determinant':str(d),'eta_zeta':str(y),'pair_guard':'determinant*eta_zeta-(pair_root**2-determinant-eta_zeta+1)**2-1-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)'},
            'restoration_note':'Retained source arithmetic rows are unchanged. Restore the six deleted positivity witnesses using the positive determinant and eta*zeta forced by the joint lemma.'
        }
        if retain:packet['zeta_restoration']=str(z0)
        (ROOT/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        results.append({'name':name,'variables':len(nvars),'rows':len(rr),'degree':degree,'residual_monomials':[len(p.terms()) for p in pp],'sum_of_squares_monomials':len(sos.terms()),'degree_witness':packet['degree_witness']})
    base_packet=json.loads((ROOT/'joint24_degree12.json').read_text())
    base_rows=[parse(e) for e in base_packet['residuals']]
    need(s.expand(base_rows[7]-parse('V+c-f*o'))==0,'monic V row')
    need(s.expand(base_rows[8]-parse('I-(2*r+1)*c**2'))==0,'monic I row')
    strong=parse('I**2-(a**2+4*a+3)*(f**2-1)')
    aux=parse('I**2*(V**2-y**2)+y**2-1')
    need(s.expand(base_rows[9]-strong)==0 and s.expand(base_rows[10]-aux)==0,'strong and auxiliary row identities')
    reduced_aux=parse('(a**2+4*a+3)*(f**2-1)*(V**2-y**2)+y**2-1')
    need(s.expand(aux-reduced_aux-parse('V**2-y**2')*strong)==0,'exact zero-set row reduction identity')
    for remove_i in [False,True]:
        restored={'V':'f*o-c'}
        replacements={sy['V']:parse(restored['V'])}
        deleted={7}
        rewritten=list(base_rows)
        if remove_i:
            restored['I']='(2*r+1)*c**2';replacements[sy['I']]=parse(restored['I'])
            deleted.add(8);rewritten[10]=reduced_aux
        rr=[s.expand(e.subs(replacements,simultaneous=True)) for i,e in enumerate(rewritten) if i not in deleted]
        nvars=[n for n in base_packet['variables'] if n not in restored]
        vr=[sy[n] for n in nvars];pp=[s.Poly(e,*vr) for e in rr]
        name='joint22_degree16' if remove_i else 'joint23_degree12'
        degree=16 if remove_i else 12
        witness=parse('a**4*f**8*o**4' if remove_i else 'eta**4*h**4*E**4')
        sos=s.Poly(sum(e*e for e in rr),*vr)
        need(len(nvars)==(22 if remove_i else 23) and len(rr)==(10 if remove_i else 11),'projected dimensions')
        need(max(p.total_degree() for p in pp)==degree//2 and sos.total_degree()==degree,'projected exact degree')
        need(sos.coeff_monomial(witness)==1,'projected coefficient certificate')
        need(set().union(*(e.free_symbols for e in rr))==set(vr+[sy[n] for n in src['fixed_numerals']]),'projected symbol closure')
        packet={k:base_packet[k] for k in ('domain','fixed_numerals','coefficient_binding','single_equation','proof','proof_status')}
        packet.update(name=name,variables=nvars,variable_count=len(nvars),residuals=[str(e) for e in rr],residual_count=len(rr),residual_degrees=[p.total_degree() for p in pp],exact_degree=degree,degree_witness={'monomial':str(witness),'coefficient':1},parent='joint24_degree12.json',full_parent_restoration=restored,auxiliary_row_reduction=('aux_new = aux_old - (V**2-y**2)*strong; strong retained' if remove_i else 'none'))
        (ROOT/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        results.append({'name':name,'variables':len(nvars),'rows':len(rr),'degree':degree,'residual_monomials':[len(p.terms()) for p in pp],'sum_of_squares_monomials':len(sos.terms()),'degree_witness':packet['degree_witness']})
    (ROOT/'BUILD_CHECK.json').write_text(json.dumps({'status':'PASS','packets':results,'scope':'Exact symbolic identities and finite degree certificates, not a proof of the inherited compiler theorem.'},indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
