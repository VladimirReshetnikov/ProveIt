"""Bounded complete76 bridge rewrites; no claimed saving or source mutation."""
from pathlib import Path
import argparse
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import sympy as s
import explore_fixed_raw_universal_76 as old


def run(rows, symbols):
    env=old.fixed_environment(symbols)
    for name,op,l,r in rows:
        assert name not in env,name
        l=env[l] if isinstance(l,str) else s.Integer(l)
        r=env[r] if isinstance(r,str) else s.Integer(r)
        env[name]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
    return env


def check(rows,eqs,syms,expected,corrections=None):
    env=run(rows,syms);corrections=corrections or {}
    rec=[]
    for ix,((l,r),target) in enumerate(zip(eqs,expected)):
        left=env[l] if isinstance(l,str) else s.Integer(l)
        right=env[r] if isinstance(r,str) else s.Integer(r)
        diff=s.expand(left-right-corrections.get(ix,0))
        sign=1 if s.expand(diff-target)==0 else -1
        assert s.expand(diff-sign*target)==0,(ix,s.factor(diff-target))
        rec.append({'index':ix,'equality':[l,r],'source':s.sstr(target),'sign':sign,
                    'correction':s.sstr(corrections.get(ix,0))})
    counts={'M':sum(op=='*' for _,op,_,_ in rows),'A':sum(op!='*' for _,op,_,_ in rows)}
    return dict(operations=len(rows),**counts,eqs=len(eqs),coordinates=len(syms)-len(old.CONSTANTS)-1,
                instructions=rows,sources=rec)


def variants():
    source=old.source_residuals(); S=old.SYM
    U=S['j']*S['c']-(2*S['r']+1)
    correction=source[12]*(U**2-S['y_aux']**2)
    out={}
    out['baseline']=check(old.SCHEDULE,old.EQUALITIES,S,source,{13:correction})
    # Shift all three endpoint/root coordinates coherently. No new q^2+1.
    names={'mu':'mu_plus','Z':'Z_minus','W':'W_plus'}
    syms={k:v for k,v in S.items() if k not in names}
    syms.update({v:s.Symbol(v,positive=True,integer=True) for v in names.values()})
    sub={S['mu']:syms['mu_plus']-1,S['Z']:syms['Z_minus']+1,S['W']:syms['W_plus']-1}
    mapped=[]
    for name,op,l,r in old.SCHEDULE:
        if name=='Lm1':continue
        if name=='gap':
            mapped.append(('Lm1','-','Lbig',1))
            mapped.append(('gap','-','Lm1','packed'))
        elif name=='norm_rhs':continue
        elif name=='mu2':
            mapped.append(('mu_minus','-','mu_plus',2))
            mapped.append(('input_norm_product','*','mu_plus','mu_minus'))
        else:mapped.append((name,op,names.get(l,l),names.get(r,r)))
    eqs=[(names.get(l,l),names.get(r,r)) for l,r in old.EQUALITIES]
    eqs[17]=('input_norm_product','scaled_kappa2')
    out['coherent_endpoint_root_shift']=check(mapped,eqs,syms,[s.expand(z.subs(sub)) for z in source],{13:correction})
    # Compute the positive difference V=mu-a*kappa instead of mu.
    V=s.Symbol('V_input',positive=True,integer=True)
    syms={k:v for k,v in S.items() if k!='mu'};syms['V_input']=V
    head=[row for row in old.SCHEDULE if row not in old.ADAPTER]
    ad=old.ADAPTER[:6]+[
      ('modulus_multiple','*','rho','a4m5'),
      ('exponent_rhs','+','W','modulus_multiple'),
      ('difference_multiple','*','kappa','a'),
      ('twice_difference','+','difference_multiple','difference_multiple'),
      ('norm_high','+','V_input','twice_difference'),
      ('input_norm_product','*','V_input','norm_high'),
      ('kappa2','*','kappa','kappa'),
      ('scaled_kappa2','*','a4m5','kappa2'),
      ('norm_rhs','+','scaled_kappa2',1)]
    eqs=list(old.EQUALITIES);eqs[17]=('input_norm_product','norm_rhs');eqs[18]=('V_input','exponent_rhs')
    out['positive_projection_difference']=check(head+ad,eqs,syms,[s.expand(z.subs(S['mu'],V+S['a']*S['kappa'])) for z in source],{13:correction})
    # Replace the input norm by the difference of the two norms and use the paid gap.
    rows=[]
    for row in old.SCHEDULE:
        if row[0] in ('kappa2','scaled_kappa2','norm_rhs'):continue
        rows.append(row)
        if row[0]=='mu2':rows += [
           ('norm_difference','-','L15','mu2'),
           ('c_plus_kappa','+','c','kappa'),
           ('gap_product','*','phi','c_plus_kappa'),
           ('scaled_gap_product','*','A','gap_product')]
    eqs=list(old.EQUALITIES);eqs[17]=('norm_difference','scaled_gap_product')
    A=S['a']**2+4*S['a']+3
    expected=list(source)
    expected[17]=S['d']**2-S['mu']**2-A*S['phi']*(S['c']+S['kappa'])
    main=S['d']**2-A*S['c']**2-1
    inp=S['mu']**2-A*S['kappa']**2-1
    gap=S['c']-S['kappa']-S['phi']
    assert s.expand(expected[17]-main+inp-A*gap*(S['c']+S['kappa']))==0
    out['shared_norm_difference']=check(rows,eqs,S,expected,{13:correction})
    assert [(v['operations'],v['M'],v['A']) for v in out.values()]==[(76,41,35),(76,41,35),(77,41,36),(77,41,36)]
    return out


def translation_regression():
    cases=0
    # Actual input Pell tuples, with bounded endpoint and a positive remainder.
    for a in (32,64,128,256):
      for u in (3,5,7,9):
        if 2**u>=a:continue
        A=a+2;Delta=A*A-1;H=4*a+3
        mu,kappa=old.previous.pell(A,u)
        W=2**u
        rho,rem=divmod(mu-a*kappa-W,H)
        assert rem==0 and rho>0
        for Z in (3,5,17,33):
          C=Z+W
          for q in (2**(C.bit_length()+1),2**(C.bit_length()+2)):
            for F in (1,3,q-1):
              mm,ww,zz=mu+1,W+1,Z-1
              assert min(mm,ww,zz)>0
              assert mm*(mm-2)==Delta*kappa*kappa
              assert mm==ww+a*kappa+rho*H and C==zz+ww
              assert q*q-Z-q*F==q*q-1-zz-q*F
              V=mu-a*kappa
              assert V==W+rho*H>0
              assert V*(V+2*a*kappa)==H*kappa*kappa+1
              cases+=1
    return dict(exact_positive_input_tuples=cases,scope='Actual input Pell bridge tuples and exact packing identities, not complete astronomical compiler/Pell tuples')


def verify():
    return dict(status='PASS_BOUNDED_76_BRIDGE_REWRITES_NO_SAVING',variants=variants(),positive=translation_regression(),
      scope='Four complete acyclic source ledgers; the translated 76 and positive-difference 77 systems are equivalent under the stated positive-domain proof. This is not a lower bound on arbitrary circuits and supplies no 75-operation theorem.')

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args=parser.parse_args()
    result=verify();dest=Path(__file__).with_suffix('.json')
    if args.write:
      dest.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    else:
      assert json.loads(dest.read_text(encoding='utf-8'))==json.loads(json.dumps(result))
    print(result['status'])
    print({k:(v['operations'],v['M'],v['A']) for k,v in result['variants'].items()})
    print(result['positive'])
