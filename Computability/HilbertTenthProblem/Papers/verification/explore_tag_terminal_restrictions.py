"""Terminal restrictions in the weakened104 sources; no complete semantics claim."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_tag_radix_divisibility_omission as base


def source_identities():
    R,H,q,L,Li,Lf,M1,Kh,B,Ns=sp.symbols('R H q L Li Lf M1 Kh B Ns')
    length=R*(L+(B-1)*M1)-Kh*(L-Li+q*Lf)
    geom=H*(R-1)-q+1
    beta1=(R-1)*(L-H)+R*(B-1)*M1-(1-Li)
    assert sp.expand(beta1-length.subs({Kh:1,Lf:1})+geom)==0
    O=L+(B-1)*M1;delta=O-3*Lf*H
    terminal=R*delta-3*(L-Li-Lf*(H-1))
    assert sp.expand(terminal-length.subs(Kh,3)+3*Lf*geom)==0
    D=sp.Symbol('D')
    scaled=D*O-(L-Li+q*Lf)
    assert sp.expand(length.subs({Kh:3,R:3*D})-3*scaled)==0
    return dict(beta1_identity=sp.sstr(beta1),terminal_identity=sp.sstr(terminal),
                source_counts=[{k:s[k] for k in ('leading','operations','multiplications','additions',
                                                 'positive_unknowns','equations')}
                               for s in (base.verify_source(0),base.verify_source(1))],
                exact_symbolic_identities=3,
                scaled_length_identity=sp.sstr(scaled))


def parity_gate():
    tested=accepted=0
    for R,H,L,Li,Lf,Kh,B,q in product(range(2),repeat=8):
        tested+=1
        if not (Li==Kh==B==q==1 and L==H):continue
        if (H*(R-1)-q+1)%2:continue
        if (R*(L+(B-1)*0)-Kh*(L-Li+q*Lf))%2:continue
        assert Lf==1;accepted+=1
    return dict(parity_assignments=tested,accepted=accepted,
                scope='All residue assignments, including even R; q,Li,Kh,B are odd and the two sources plus containment hold modulo2.')


def beta1_gate():
    tested=0
    for R in range(10,80):
        for H in (1,2,3,10,100):
            q=(R-1)*H+1
            for Ns in (1,2,5):
                L=2*Ns+H
                for B in (3,9,27):
                    for M1 in (0,1,3):
                        Li=3
                        obstruction=(R-1)*(L-H)+R*(B-1)*M1
                        assert obstruction>0>1-Li
                        tested+=1
    return dict(positive_obstructions=tested,
                scope='Illustrations of the sign contradiction, not complete source solutions.')


def short_geometry_gate():
    tested=boundary=0
    for H in (1,2,3,10,100,1000):
        for R in (max(270,28*H),max(270,29*H),max(270,100*H)):
            q=(R-1)*H+1
            assert q<=R*H and Fraction(27*q,R-3)<28*H
            for Lf in (1,3,5,7):
                upper=Fraction(84*H,R)
                lower=-Fraction(1,9)-Fraction(21*H,R)
                assert -1<lower and upper<=3
                # Delta is strictly between these bounds, including upper=3.
                assert [d for d in range(-9,10,3) if lower<d<upper]==[0]
                boundary+=R==28*H
                tested+=1
    # D,Li,q divisible9 imply L=0 mod9 before any bound on Delta.
    transport_cases=transport_survivors=0
    for L,O,Lf in product(range(9),range(9),(1,3,5,7)):
        transport_cases+=1
        if (0*O-(L-0+0*Lf))%9:continue
        assert L==0;transport_survivors+=1
    # No carries in M0+M1 force both markers0 mod9, so O and3LfH make Delta3-divisible.
    residue_cases=0
    bits=[0,1,3,4]
    for M0,M1,Lf in product(bits,bits,(1,3,5,7)):
        if (M0+M1)%9:continue
        assert M0==M1==0
        for B in (3,9,27):
            if (M0+B*M1-3*Lf)%9:continue
            assert Lf==3;residue_cases+=1
    return dict(rational_bounds=tested,exact_R_eq_28H_cases=boundary,
                transport_mod9_cases=transport_cases,transport_mod9_survivors=transport_survivors,
                accepted_mod9_residues=residue_cases,
                scope='Conditional R>=28H proof: exact rational strict bounds, the unconditional scaled-length residue, and complete low two-trit mask residues. This is not a search of all unrestricted104 witnesses.')


def verify():
    return dict(status='PASS_TAG_TERMINAL_RESTRICTIONS',sources=source_identities(),
                parity=parity_gate(),beta1=beta1_gate(),short_geometry=short_geometry_gate(),
                proof='../1980/EXPLORATION_TAG_TERMINAL_RESTRICTIONS.md',
                review=dict(current_28H='Author and two independent complete proof/source reviews and fresh verification runs PASS on the strengthened28H theorem; proof and arithmetic frozen.',
                            predecessor_100H='Author, root and algebra complete proof/source reviews and fresh verification PASS. These historical gates do not constitute review of the strengthened28H theorem.'),
                scope='Lfinal is odd, beta1 is unsatisfiable, and beta2 with R>=28H has Lfinal3. General beta2 terminal5/7 and weakened104 halting semantics remain open.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print({k:v for k,v in result.items() if k not in ('sources','proof','review','scope')})
