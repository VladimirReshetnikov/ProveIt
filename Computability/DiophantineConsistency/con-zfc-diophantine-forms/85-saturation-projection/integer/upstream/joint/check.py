#!/usr/bin/env python3
"""Independent standard-library exact sparse verification; no builder imports."""
from pathlib import Path
import ast, gzip, hashlib, json, math, sys

ROOT=Path(__file__).resolve().parent
sys.setrecursionlimit(20000)

def need(ok, message):
    if not ok: raise ValueError(message)

def main():
    pin=json.loads((ROOT/'SOURCE_PIN.json').read_text())
    raw=(ROOT/pin['copy']).read_bytes()
    need(hashlib.sha256(raw).hexdigest()==pin['sha256'],'parent byte identity')
    need((ROOT/pin['parent']).read_bytes()==raw,'parent agrees with live sibling component')
    source=json.loads(raw)
    packets=[json.loads((ROOT/(n+'.json')).read_text()) for n in ('joint25_octic','joint24_degree12')]
    names=sorted(set(source['variables']+source['fixed_numerals']+sum((p['variables'] for p in packets),[])))
    index={n:i for i,n in enumerate(names)}
    zero=(0,)*len(names)
    one={zero:1}
    def add(a,b,sgn=1):
        out=dict(a)
        for e,c in b.items():
            out[e]=out.get(e,0)+sgn*c
            if not out[e]:del out[e]
        return out
    def mul(a,b):
        out={}
        for ea,ca in a.items():
            for eb,cb in b.items():
                e=tuple(x+y for x,y in zip(ea,eb));out[e]=out.get(e,0)+ca*cb
        return {e:c for e,c in out.items() if c}
    def power(a,n):
        r=one
        while n:
            if n&1:r=mul(r,a)
            n//=2
            if n:a=mul(a,a)
        return r
    atoms={}
    for n,i in index.items():
        e=list(zero);e[i]=1;atoms[n]={tuple(e):1}
    def parse(text,replace=None):
        env=dict(atoms);env.update(replace or {})
        def go(n):
            if isinstance(n,ast.Expression):return go(n.body)
            if isinstance(n,ast.Name) and n.id in env:return env[n.id]
            if isinstance(n,ast.Constant) and type(n.value)==int:return {zero:n.value} if n.value else {}
            if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {e:-c for e,c in go(n.operand).items()}
            if isinstance(n,ast.BinOp):
                a=go(n.left)
                if isinstance(n.op,ast.Pow):
                    need(isinstance(n.right,ast.Constant) and type(n.right.value)==int and 0<=n.right.value<=16,'fixed bounded exponent')
                    return power(a,n.right.value)
                b=go(n.right)
                if isinstance(n.op,ast.Add):return add(a,b)
                if isinstance(n.op,ast.Sub):return add(a,b,-1)
                if isinstance(n.op,ast.Mult):return mul(a,b)
            raise ValueError('Disallowed expression '+ast.dump(n))
        return go(ast.parse(text,mode='eval'))
    q=parse('beta*(3*J3+1)+1')
    U=parse('cone_A*F');W=mul(atoms['cone_B'],add(add(q,atoms['F'],-1),atoms['alpha'],-1))
    determinant=add(mul(U,W),power(add(add(q,U,-1),W,-1),2),-1)
    zeta0=parse('1-V+j*c+h*E-eta')
    y0=mul(atoms['eta'],zeta0)
    oldpos1=parse('1+eta_zeta_pos1**2+eta_zeta_pos2**2+eta_zeta_pos3*(eta_zeta_pos3+1)')
    oldpos2=parse('1+cone1**2+cone2**2+cone3*(cone3+1)')
    need(parse(source['residuals'][-2])==add(y0,oldpos1,-1),'literal parent eta guard')
    need(parse(source['residuals'][-1])==add(determinant,oldpos2,-1),'literal parent determinant guard')
    pos=parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
    t2=parse('pair_root**2')
    retained=[parse(e) for e in source['residuals'][:-2]]
    base=[n for n in source['variables'] if not n.startswith(('eta_zeta_pos','cone'))]
    results=[]
    for p in packets:
        retain='zeta' in p['variables']
        expected_vars=base+(['zeta'] if retain else [])+['pair_root','pair_pos1','pair_pos2','pair_pos3']
        need(p['variables']==expected_vars and len(set(p['variables']))==len(expected_vars),'exact coordinate list')
        need(p['fixed_numerals']==source['fixed_numerals'],'whole fixed tuple unchanged')
        need(p['parent_sha256']==pin['sha256'],'packet source pin')
        y=mul(atoms['eta'],atoms['zeta']) if retain else y0
        inside=add(add(add(t2,determinant,-1),y,-1),one)
        guard=add(add(mul(determinant,y),power(inside,2),-1),pos,-1)
        expected=retained+([add(atoms['zeta'],zeta0,-1)] if retain else [])+[guard]
        rows=[parse(e) for e in p['residuals']]
        need(rows==expected,'all exact residual identities '+p['name'])
        need(len(rows)==p['residual_count']==(13 if retain else 12),'row count')
        need(len(p['variables'])==p['variable_count']==(25 if retain else 24),'variable count')
        live={names[i] for row in rows for e in row for i,v in enumerate(e) if v}
        need(live==set(p['variables']+p['fixed_numerals']),'all and only declared symbols')
        vi=[index[n] for n in p['variables']]
        degrees=[max(sum(e[i] for i in vi) for e in row) for row in rows]
        need(degrees==p['residual_degrees'] and 2*max(degrees)==p['exact_degree'],'degree upper bounds')
        witness=parse(p['degree_witness']['monomial'])
        need(len(witness)==1 and next(iter(witness.values()))==1,'degree monomial form')
        we=next(iter(witness));remaining={}
        for row in rows:
            eligible=[(e,c) for e,c in row.items() if all(e[i]<=we[i] for i in vi)]
            for ea,ca in eligible:
                for eb,cb in eligible:
                    if all(ea[i]+eb[i]==we[i] for i in vi):
                        ce=tuple(ea[i]+eb[i] if i not in vi else 0 for i in range(len(names)))
                        remaining[ce]=remaining.get(ce,0)+ca*cb
        remaining={e:c for e,c in remaining.items() if c}
        need(remaining=={zero:1},'fixed-slice exact degree coefficient')
        need(p['degree_witness']['coefficient']==1,'recorded coefficient')
        # A changed constant in the new guard is rejected by the identity comparison.
        need(add(guard,one)!=guard,'changed-constant negative control')
        results.append({'name':p['name'],'variables':len(p['variables']),'rows':len(rows),'degree':p['exact_degree'],'degree_witness':p['degree_witness'],'status':'PASS'})
    projected=[parse(e,{'zeta':zeta0}) for e in packets[0]['residuals']]
    need(projected[-2]=={},'zeta row vanishes under restoration')
    need(projected[:-2]+projected[-1:]==[parse(e) for e in packets[1]['residuals']],'exact 25-to-24 projection')
    binding=json.loads((ROOT/'../guards/COEFFICIENT_BINDING.json').read_text())
    values={}
    for n in source['fixed_numerals']:
        record=binding['payloads'][n]
        for p in packets:need(p['coefficient_binding']['ports'][n]=='../guards/'+record['path'],'coefficient path')
        packed=(ROOT/'../guards'/record['path']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(raw).hexdigest()==record['raw_sha256'],'raw coefficient SHA256 '+n)
        need(hashlib.sha256(packed).hexdigest()==record['gzip_sha256'],'gzip coefficient SHA256 '+n)
        need(len(raw)==record['raw_bytes'] and raw[-1]!=0,'minimal coefficient bytes '+n)
        values[n]=int.from_bytes(raw,'little');need(values[n].bit_length()==record['bits'],'coefficient bits '+n)
    need(values['beta']==2**1064921-1,'native fixed radix')
    need(values['cone_A']==2**1113 and values['cone_B']==2**666104,'fixed determinant scales')
    positives=0
    for x in range(1,301):
        for y in range(1,301):
            n=x+y-1;m=math.isqrt(n);t=m if n-m*m<=m else m+1
            need(x*y-(t*t-x-y+1)**2>0,'constructive positive pair diagnostic');positives+=1
    signed=0
    for x in range(-30,31):
        for y in range(-30,31):
            for t in range(-20,21):
                need(x*y-(t*t-x-y+1)**2<=0 or (x>0 and y>0),'unrestricted signed diagnostic');signed+=1
    result={'status':'PASS','packets':results,'exact_projection':True,'coefficient_bytes_verified':True,'positive_pairs_tested':positives,'signed_triples_tested':signed,'scope':'Independent exact polynomial identities and coefficient bindings; finite diagnostics do not replace the universal mathematical proof or inherited native calibration.'}
    output=ROOT/('CHECK_optimized.json' if not __debug__ else 'CHECK_normal.json')
    output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
