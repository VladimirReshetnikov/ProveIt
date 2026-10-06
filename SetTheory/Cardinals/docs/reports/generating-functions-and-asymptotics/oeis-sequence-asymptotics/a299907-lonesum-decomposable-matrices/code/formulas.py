"""Displayed coefficient formulas and numerical inverse centers."""
import sympy as S
import mpmath as mp

def coefficient_formulas(L):
    c1=-S.sqrt(2)*(167*L**3-143*L**2-L+1)/(192*L**S.Rational(3,2)*(L-1))
    c2=(65041*L**6-108866*L**5+42099*L**4+1724*L**3-573*L**2-2*L+1)/(36864*L**3*(L-1)**2)
    return c1,c2

def constants():
    L=mp.log(2)
    beta=mp.sqrt(2/L)
    C=mp.exp(-mp.mpf(5)/8+1/(8*L))/(mp.pi*(2*L)**mp.mpf('.25')*mp.sqrt(1-L))
    c1=-mp.sqrt(2)*(167*L**3-143*L**2-L+1)/(192*L**mp.mpf('1.5')*(L-1))
    c2=(65041*L**6-108866*L**5+42099*L**4+1724*L**3-573*L**2-2*L+1)/(36864*L**3*(L-1)**2)
    return L,beta,C,c1,c2

def inverse_centers(log_T):
    if log_T <= 0:
        raise ValueError('log T must be positive')
    L,beta,C,c1,_=constants()
    x=log_T/(2*mp.lambertw(log_T/(2*mp.e*L)))
    h=mp.log(x/L);k=mp.log(2*mp.pi*C)
    D1=(mp.log(x)/4-k)/(2*h)+beta**2/(8*h*h)-beta**2/(8*h**3)
    X1=x-beta*mp.sqrt(x)/(2*h)+D1
    D2=-(c1+beta*D1*(mp.mpf('.5')-1/h)+beta/(8*h)+beta**3/(24*h**3)-beta**3/(32*h*h))/(2*h*mp.sqrt(x))
    return x,h,X1,X1+D2
