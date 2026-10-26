"""Independent exact audit of P216 ports and retained frame identities.

No producer module is imported.  Only the standard library is used.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PARENT = ROOT / 'pooled/ConZFC_Pooled_Projection_2026-10-25'
OUTPUT = ROOT / 'P216_PORTS_AUDIT.json'

def read(path):
    return json.loads(path.read_text())

def dec(a):
    d = {}
    for c, m in a:
        if type(c) is not int or any(type(i) is not int for i in m):
            raise ValueError('noninteger sparse term')
        t = tuple(sorted(m))
        d[t] = d.get(t, 0) + c
    return {m:c for m,c in d.items() if c}

def enc(d):
    return [[c,list(m)] for m,c in sorted(d.items()) if c]

def add(*args):
    d = {}
    for a in args:
        for m,c in a.items(): d[m] = d.get(m,0)+c
    return {m:c for m,c in d.items() if c}

def sc(c,a): return {m:c*v for m,v in a.items() if c*v}
def sub(a,b): return add(a,sc(-1,b))
def mul(a,b):
    d = {}
    for m,c in a.items():
        for n,e in b.items():
            t = tuple(sorted(m+n)); d[t] = d.get(t,0)+c*e
    return {m:c for m,c in d.items() if c}
def sq(a): return mul(a,a)
def co(c): return {():c} if c else {}
def va(i): return {(i,):1}
def require(v, message):
    if not v: raise ValueError(message)
def equal(a,b,message): require(a==b,message+': '+str(enc(sub(a,b)))[:300])
def subst(a,mp):
    out = {}
    for m,c in a.items():
        term=co(c)
        for i in m: term=mul(term,mp.get(i,va(i)))
        out=add(out,term)
    return out

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--parent',type=Path,default=PARENT)
    parser.add_argument('--output',type=Path,default=OUTPUT)
    args=parser.parse_args();parent=args.parent
    final_path=parent/'algebra/equation216.json'
    final=read(final_path)
    affine=read(parent/'algebra/affine216.json')
    old=read(parent/'algebra/parent223.json')
    frame=read(parent/'composition/composed/FRAME_CHECK.json')
    final_names={v['name']:i for i,v in enumerate(final['variables'])}
    require(len(final_names)==216,'unique final variable names')
    rows=[dec(r['terms']) for r in final['residuals']]
    affine_rows=[dec(r['terms']) for r in affine['residuals']]
    require(len(rows)==153,'153 parent rows')
    deleted_variables=set([141,142,143,144,145,146,212,213,214,215])
    deleted_rows=set([97,98,99,100,101,102,149,150,151,152])
    observed={j for j,r in enumerate(rows) if deleted_variables & {i for m in r for i in m}}
    require(observed==deleted_rows,'private support appears only in deleted rows')

    # Independently reverse every elementary integer row operation.
    rowmaps=[{j:1} for j in range(153)]
    recovered=list(rows)
    ops=read(parent/'algebra/row_certificate216.json')['operations']
    for i,j,c in reversed(ops):
        require(i!=j and type(c) is int,'elementary row operation')
        recovered[i]=add(recovered[i],sc(-c,recovered[j]))
        rr=dict(rowmaps[i])
        for k,v in rowmaps[j].items(): rr[k]=rr.get(k,0)-c*v
        rowmaps[i]={k:v for k,v in rr.items() if v}
    require(recovered==affine_rows,'59 inverse row operations exactly reconstruct affine216')

    # All surviving semantic ports use retained named coordinates except J,
    # which is the printed restoration in the last affine projection.
    J=dec(read(parent/'algebra/affine_certificate216.json')['restoration_terms_original_indices'])
    old_to_final={}
    for i,v in enumerate(old['variables']):
        if v['name']=='add.380': old_to_final[i]=J
        elif v['name'] in final_names: old_to_final[i]=va(final_names[v['name']])
    def port(p):
        require(all(i in old_to_final for _,m in p for i in m),'port has authenticated named transport')
        return subst(dec(p),old_to_final)
    atoms=[{'label':a['label'],'terms':enc(port(a['terms']))} for a in frame['atoms']]
    A=add(va(134),co(1)); W=va(133)
    F=add(W,co(-2),*(sc(-1,sq(dec(a['terms']))) for a in atoms))
    equal(F,affine_rows[129],'36-square frame after projections')
    require(not(set(rowmaps[129])&deleted_rows),'frame recovery uses no deleted row')

    requests=[]
    pair_for={0:0,1:12,2:12,3:2,4:0,5:3,7:5,8:6,9:7,10:8,11:9,12:10,13:11,14:12,15:13,16:14,17:15}
    start_for={0:138,2:147,3:150,5:153,6:156,7:159,8:162,9:165,10:168,11:171,12:174,13:177,14:180,15:183}
    ay_rows={0:95,2:103,3:105,5:107,6:109,7:111,8:113,9:115,10:117,11:119,12:121,13:123,14:125,15:127}
    pairs={}
    for item in frame['requests']:
        rid=item['request']; pid=pair_for[rid]; start=start_for[pid]
        D=va(start); Y=add(va(start+1),co(-1 if pid==3 else 0))
        Z=add(va(start+2),co(1 if pid==12 else 0)); X=add(D,Z)
        base,index,output=(port(item[k]) for k in ['base','index','output'])
        require(all(p in [dec(a['terms']) for a in atoms] for p in [base,index,output]),'every request port is a frame atom')
        ay=ay_rows[pid]; norm=ay+1
        equal(sub(Z,mul(A,Y)),rows[ay],'actual A*Y request '+str(rid))
        equal(add(sq(X),sq(Y),sc(-1,sq(Z)),co(-1)),rows[norm],'actual norm request '+str(rid))
        pairs[pid]=(X,Y,Z,D,index,norm)
        requests.append({'request':rid,'pair':pid,'base':enc(base),'index':enc(index),'output':enc(output),
                         'X':enc(X),'Y':enc(Y),'Z':enc(Z),'D':enc(D),'AY_row':ay,'norm_row':norm})
    require(len(pairs)==14 and len(requests)==17,'14 signed pairs and 17 requests')

    # Restore the actual signed-index aggregate, undoing the deliberate norm
    # subtraction from the difference-coordinate presentation.
    orient=add(*(add(sq(add(X,co(-1))),sq(sub(Y,k))) for X,Y,Z,D,k,nr in pairs.values()),sc(-1,mul(va(134),va(201))))
    normsum=add(*(rows[nr] for X,Y,Z,D,k,nr in pairs.values()))
    equal(orient,add(affine_rows[142],normsum),'canonical signed-index aggregate')
    orient_map=dict(rowmaps[142])
    for X,Y,Z,D,k,nr in pairs.values():orient_map[nr]=orient_map.get(nr,0)+1
    orient_map={k:v for k,v in orient_map.items() if v}
    require(not(set(orient_map)&deleted_rows),'orientation recovery uses no deleted row')

    # Exact source bindings for both old pools and all singleton ports.
    byid={x['request']:x for x in requests}
    groups=[('t',[0],0),('B',[1],1),('BH',[2],2),('q',[4,11,14],None),('q+1',[3,5,7,8,9,10,12,13,15,16,17],None)]
    group_records=[]
    for name,ids,singleton in groups:
        n=dec(byid[ids[0]]['base']);T=add(sc(2,mul(A,n)),sc(-1,sq(n)),co(-1))
        H=add(*(mul(dec(byid[i]['Y']),sub(dec(byid[i]['output']),dec(byid[i]['X']))) for i in ids))
        S=add(*(sub(sq(sub(dec(byid[i]['output']),dec(byid[i]['D']))),sq(dec(byid[i]['Y']))) for i in ids))
        E=sub(S,sc(2,mul(n,H)))
        if singleton is not None:
            ti=141+2*singleton;qi=ti+1;r=97+2*singleton
            target=sub(va(ti),T)
            equal(target if singleton<2 else sc(-1,target),rows[r],'singleton modulus '+name)
            item=byid[ids[0]]
            delta=add(dec(item['output']),sc(-1,dec(item['D'])),sc(-1,mul(n,dec(item['Y']))))
            equal(add(delta,mul(va(ti),va(qi))),rows[r+1],'singleton quotient '+name)
        else:
            K,L,rr=(214,215,151) if name=='q' else (212,213,149)
            equal(add(va(K),sc(-2,H),sc(-1,mul(sub(sc(2,A),n),va(L)))),rows[rr],'old pooled bilinear '+name)
            equal(add(S,sc(-1,mul(n,va(K))),va(L)),rows[rr+1],'old pooled norm '+name)
        group_records.append({'name':name,'requests':ids,'base':enc(n),'T':enc(T),'H':enc(H),'S':enc(S),'E':enc(E)})

    # Bootstrap identities are recovered from affine216.  Required rows are
    # explicit and the tracked row combinations avoid every deleted row.
    t,x,yp,Fv,B,C=va(0),va(1),va(2),va(3),va(4),sc(2,va(16))
    Hactual=add(co(2),sc(4,add(C,add(va(8),co(-1)),*(va(i) for i in range(9,16)))))
    expected_bootstrap={
        'horizon':add(t,co(-16),sc(-4,sq(va(187)))),
        'B_odd_product':add(C,Fv,co(1),sc(-1,mul(B,va(18)))),
        'initial_endpoint':add(x,sc(-1,Fv),co(-1),sc(-1,mul(yp,va(5)))),
        'terminal_divisor':sub(va(7),add(co(1),mul(add(t,co(1)),add(yp,co(-1))))),
        'terminal_endpoint':add(x,co(-1),sc(-1,mul(va(7),va(6)))),
        'odd_beta_spacing':add(yp,co(-1),sc(-1,Fv),sc(-2,mul(Fv,va(210)))),
        'BH_definition':sub(va(186),mul(B,Hactual))}
    boot_results={}
    for label,poly in expected_bootstrap.items():
        matches=[j for j,r in enumerate(affine_rows) if r==poly or r==sc(-1,poly)]
        # Endpoint row1 was combined with row2 in the final chart; affine
        # source contains the literal endpoint, so its inverse is recorded.
        require(len(matches)==1,'literal bootstrap row '+label)
        j=matches[0];sign=1 if affine_rows[j]==poly else -1
        mp={k:sign*v for k,v in rowmaps[j].items()}
        require(not(set(mp)&deleted_rows),'bootstrap avoids deleted rows '+label)
        boot_results[label]={'terms':enc(poly),'final_row_combination':[[v,k] for k,v in sorted(mp.items())]}

    # The raw index bound needed by the proposed orientation+power fusion
    # precedes row142. Bind all anchor/cap hypotheses independently.
    anchorX=add(va(183),va(185));anchorY=va(184)
    auxX,auxY,cmpX,cmpY=va(188),va(189),va(190),va(191)
    cmpBase=add(va(192),co(1))
    otherYs=[Y for pid,(X,Y,Z,D,k,nr) in pairs.items() if pid!=15]
    slack=add(sq(va(204)),sq(va(205)),mul(va(206),add(va(206),co(1))))
    cap=add(sq(anchorY),co(-1),sc(-1,sq(J)),*(sc(-1,sq(Y)) for Y in otherYs),sc(-1,slack))
    raw_anchor={
        'large_center_ordinate':(92,sub(va(136),mul(W,add(sc(2,va(135)),co(-1))))),
        'large_center_product':(93,sub(va(137),mul(add(W,co(1)),va(136)))),
        'large_center_norm':(94,add(sq(A),sq(va(136)),sc(-1,sq(va(137))),co(-1))),
        'auxiliary_product':(132,sub(va(198),mul(A,auxY))),
        'auxiliary_norm':(133,add(sq(auxX),sq(auxY),sc(-1,sq(va(198))),co(-1))),
        'comparison_product':(134,sub(va(199),mul(cmpBase,cmpY))),
        'comparison_norm':(135,add(sq(cmpX),sq(cmpY),sc(-1,sq(va(199))),co(-1))),
        'anchor_square':(136,sub(va(200),sq(anchorY))),
        'odd_multiple':(137,sub(auxY,mul(add(sc(2,va(194)),co(1)),va(200)))),
        'comparison_base':(138,sub(va(192),sc(4,mul(auxY,add(sc(2,va(193)),co(1)))))),
        'base_congruence':(139,add(cmpBase,sc(-1,A),sc(-1,mul(auxX,va(195))))),
        'abscissa_congruence':(140,add(cmpX,sc(-1,anchorX),sc(-1,mul(auxX,va(196))))),
        'index_congruence':(141,add(cmpY,sc(-1,J),sc(-4,mul(anchorY,va(197))))),
        'strict_squared_cap':(146,cap)}
    raw_results={}
    for label,(j,p) in raw_anchor.items():
        equal(p,affine_rows[j],'raw anchor '+label)
        require(not(set(rowmaps[j])&(deleted_rows|{142})),'raw cap avoids all power and orientation rows '+label)
        raw_results[label]={'terms':enc(p),'final_row_combination':[[v,k] for k,v in sorted(rowmaps[j].items())]}
    require([j for j,r in enumerate(rows) if any(201 in m for m in r)]==[142],'orientation quotient private to row142')

    result={
        'schema':'independent_p216_power_ports_v1','status':'passed',
        'parent_sha256':hashlib.sha256(final_path.read_bytes()).hexdigest(),
        'domain':'unrestricted integers','old_variable_count':216,
        'A':enc(A),'W':enc(W),'derived_index_J':enc(J),
        'deleted_variables':sorted(deleted_variables),'deleted_rows':sorted(deleted_rows),
        'frame_atoms':atoms,'frame_residual':enc(F),
        'frame_final_row_combination':[[v,k] for k,v in sorted(rowmaps[129].items())],
        'orientation_final_row_combination':[[v,k] for k,v in sorted(orient_map.items())],
        'bootstrap':boot_results,'raw_anchor_before_orientation':raw_results,
        'orientation_quotient_private_coordinate':201,'orientation_quotient_private_row':142,
        'requests':requests,'groups':group_records,
        'proof_boundary':'Exact polynomial identities and row support are checked. The unbounded signed-Pell canonical-index and large-A frame theorems remain the identified inherited ordinary mathematical dependencies; this is not a new proof-assistant build.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'passed','requests':17,'pairs':14,'frame_atoms':36,'private_variables':10,'private_rows':10,'output':str(args.output)}))

if __name__=='__main__':main()
