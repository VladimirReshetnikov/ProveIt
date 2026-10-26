#!/usr/bin/env python3
"""Literal eleven-positive constant-dilation Lucas-correction circuit."""
import argparse, json
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parent
LAMBDA = 210

def construct():
    rows=[]
    def g(name,op,a,b):
        rows.append([name,op,a,b]);return name
    h=g('h','*','beta','J')
    q=g('q','+',h,1)
    q2=g('q2','*',q,q)
    q4=g('q4','*',q2,q2)
    q3=g('q3','*',q2,q)
    q7=g('q7','*',q4,q3)
    qF=g('qF','-',q,'F')
    C=g('C','-',qF,'alpha')
    X=g('X','*',q,'w')
    k=g('k','+','eta','zeta')
    ks=g('ks','*',k,'s')
    c=g('c','+',ks,'eta')
    Xs=g('Xs','*',X,'s')
    Xsps=g('Xsps','+',Xs,'s')
    Am1=g('Am1','*',LAMBDA,Xsps)
    Ap1=g('Ap1','+',Am1,2)
    Delta=g('Delta','*',Am1,Ap1)
    fourAm1=g('fourAm1','*',4,Am1)
    H=g('H','-',fourAm1,1)
    v0=g('v0','*',Xs,'s')
    ell0=g('ell0','*',v0,k)
    ell=g('ell','*',LAMBDA**2,ell0)
    ellpk=g('ellpk','+',ell,k)
    ellprod=g('ellprod','*',ell,ellpk)
    E=g('E','+',ellprod,1)
    g1=g('g1','*',h,qF)
    mask=g('mask','+',g1,'alpha')
    q2m1=g('q2m1','-',q2,1)
    maskpart=g('maskpart','*',mask,q2m1)
    qMF=g('qMF','*',q,'MF')
    masksum=g('masksum','+','MC',qMF)
    masksumJ=g('masksumJ','*',masksum,'J')
    R=g('R','+',maskpart,masksumJ)
    Rp1=g('Rp1','+',R,1)
    e=g('e','-',k,Rp1)
    k2=g('k2','*',k,k)
    k2m4=g('k2m4','-',k2,4)
    ell0factor=g('ell0factor','*',ell0,k2m4)
    a2=g('a2','*',27,k2)
    a2p8=g('a2p8','+',a2,8)
    k4=g('k4','*',k2,k2)
    a3hi=g('a3hi','*',675,k4)
    a3mid=g('a3mid','*',324,k2)
    a3diff=g('a3diff','-',a3hi,a3mid)
    a3=g('a3','+',a3diff,160)
    vc3=g('vc3','*',LAMBDA**6//15120,v0)
    vc3a3=g('vc3a3','*',vc3,a3)
    c2a2=g('c2a2','*',LAMBDA**4//360,a2p8)
    highminus=g('highminus','-',vc3a3,c2a2)
    vv=g('vv','*',v0,highminus)
    cb=g('cb','+',vv,LAMBDA**2//6)
    correction=g('correction','*',ell0factor,cb)
    estar=g('estar','-',e,correction)
    q4s=g('q4s','*',q4,'s')
    ec=g('ec','-',estar,q4s)
    K0w=g('K0w','+','K0','w')
    KC=g('KC','*',K0w,C)
    B=g('B','-',KC,'F')
    c2=g('c2','*',c,c)
    U=g('U','*','i',c2)
    UE=g('UE','*',U,E)
    DUE=g('DUE','*',Delta,UE)
    a=g('a','*',DUE,U)
    F0=g('F0','+',a,1)
    aF=g('aF','*',a,F0)
    fouraF=g('fouraF','*',4,aF)
    f=g('f','+',a,F0)
    Q=g('Q','*',Delta,fouraF)
    G=g('G','*',E,F0)
    cT=g('cT','*',c,'T')
    b=g('b','-',cT,R)
    fb=g('fb','*',f,b)
    V=g('V','-',fb,c)
    L=g('L','*',b,V)
    LB=g('LB','*',L,B)
    nk=g('nk','+','n','kappa')
    center=g('center','-',nk,LB)
    M=g('M','*',h,q7)
    Mcenter=g('Mcenter','*',M,center)
    q7B=g('q7B','*',q7,B)
    hec=g('hec','*',h,ec)
    tail=g('tail','+',q7B,hec)
    Z=g('Z','-',Mcenter,tail)
    M2=g('M2','*',M,M)
    MG=g('MG','*',M2,G)
    V2=g('V2','*',V,V)
    MGV2=g('MGV2','*',MG,V2)
    Z2=g('Z2','*',Z,Z)
    inside=g('inside','-',Z2,MGV2)
    Qinside=g('Qinside','*',Q,inside)
    rest=g('rest','-',MG,Z2)
    P0=g('P0','+',Qinside,rest)
    threec=g('threec','*',3,c)
    twoX=g('twoX','*',2,X)
    gap=g('gap','-',threec,twoX)
    Xgap=g('Xgap','*',X,gap)
    K=g('K','+',Xgap,2)
    kapH=g('kapH','*','kappa',H)
    N=g('N','-',K,kapH)
    threeN=g('threeN','*',3,N)
    factorN=g('factorN','+',threeN,1)
    factorP=g('factorP','+',P0,1)
    prod=g('prod','*',factorN,factorP)
    out=g('P','-',prod,1)
    parent=json.loads((ROOT/'171-positive.json').read_text())
    binding=dict(parent['coefficient_binding'])
    binding['path']='source140/coefficients/'
    return {
      'name':'constant_dilation210_inverse3_positive11',
      'domain':'strictly positive integers',
      'witnesses':['J','F','alpha','i','T','w','s','n','eta','zeta','kappa'],
      'fixed_numerals':['beta','K0','MC','MF'],
      'coefficient_binding':binding,
      'lambda':LAMBDA,'source':rows,'output':out,
      'operations':len(rows),'operation_breakdown':dict(Counter(r[1]for r in rows)),
      'exact_degree':174,
      'proof':'PROOF_constant_dilation.md',
      'status':'Ordinary proof with an independent AI-assisted mathematical audit; inherited native calibration; no end-to-end kernel certificate.'
    }

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true',help='verify the retained graph byte-for-byte without writing it')
    args=parser.parse_args()
    p=construct();out=ROOT/'constant_dilation11.json'
    serialized=json.dumps(p,indent=2)+'\n'
    if args.check:
        if out.read_bytes()!=serialized.encode('utf-8'):
            raise SystemExit('retained graph differs from deterministic construction')
    else:
        out.write_text(serialized)
    print(json.dumps({k:p[k]for k in ['name','operations','operation_breakdown','exact_degree']},indent=2))
