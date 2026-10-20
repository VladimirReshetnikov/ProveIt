"""Own finite Hilbert bridge check, using the pinned reviewed K/S proof kernel.
No QS or old rho4 is an axiom of any checked output. No machine execution.
"""
from pathlib import Path
import hashlib, json
assert hashlib.sha256(Path(__file__).with_name('hilbert.py').read_bytes()).hexdigest() == '63396d6ec0b98744b8b4502c316fbdb7fdb018dcda1dbaed0d2e612e5351b7cc'
import hilbert as h
I,Q,R,N,NN,P = h.I,h.Q,h.R,h.N,h.NN,h.P

def trans(p,q):
    a,b=h.form(p)[1:]; assert h.form(q)[1]==b
    x=h.hyp(a); return h.ded(x,h.mp(q,h.mp(p,x)))
def contra(p):
    a,b=h.form(p)[1:]; x=h.hyp(N(b));y=h.hyp(a)
    return h.ded(x,h.ded(y,h.mp(x,h.mp(p,y))))
def dn(a):
    x=h.hyp(a);return h.ded(x,h.double(x))
def dnmap(p):return contra(contra(p))
def imap(p,q):
    aa,a=h.form(p)[1:];b,bb=h.form(q)[1:]
    f=h.hyp(I(a,b));x=h.hyp(aa)
    return h.ded(f,h.ded(x,h.mp(q,h.mp(f,h.mp(p,x)))))
def cov(a,p):return imap(h.ident(a),p)
def neg_dn_elim(a):
    x=h.hyp(N(NN(a)));y=h.hyp(a)
    return h.ded(x,h.ded(y,h.mp(x,h.mp(dn(a),y))))
def neg_dn_intro(a):
    x=h.hyp(N(a));y=h.hyp(NN(a))
    return h.ded(x,h.ded(y,h.mp(y,x)))
def implication_dn(a,b):
    f=h.hyp(I(a,b));nb=h.hyp(N(b));aa=h.hyp(a)
    na=h.ded(aa,h.mp(nb,h.mp(f,aa)))
    nna=h.hyp(NN(a))
    # f remains a temporary premise; no open premise is generalized.
    return h.ded(f,h.ded(nna,h.ded(nb,h.mp(nna,na))))

a,b,c,i,j,z=map(P,('a','b','c','i','j','z'));out={}
out['negated_double_negation_elim']=neg_dn_elim(z)
out['negated_double_negation_intro']=neg_dn_intro(z)

# All symbols below are already co-translated numeric parameters. The matrix
# and private label are literally the same parameter c.
sub=Q(c,I(R(c,a),R(c,b))); req=h.req(b,c,c)
x=I(sub,req);xp=I(NN(sub),NN(req))
p=implication_dn(sub,req);assert h.form(p)==I(x,xp)
p=contra(h.normal(a,p))
p=cov(c,p)
p=contra(h.normal(a,p))
p=cov(R(b,c),p)
p=h.normal(b,p)
cl=h.clos(a,b,c,c)
clp=NN(Q(b,I(R(b,c),N(Q(a,I(c,N(Q(a,xp))))))))
assert h.form(p)[1]==cl
cl_bridge=trans(p,dn(h.form(p)[2]));assert h.form(cl_bridge)==I(cl,clp)
out['literal_closure_forward']=cl_bridge
inner=I(cl,N(req));innerp=I(clp,N(NN(req)))
ip=imap(cl_bridge,neg_dn_elim(req));assert h.form(ip)==I(innerp,inner)
out['literal_inner_backward']=ip
core=Q(c,inner);corep=NN(Q(c,innerp))
core_bridge=dnmap(h.normal(c,ip));assert h.form(core_bridge)==I(corep,NN(core))
out['literal_core_to_double_core']=core_bridge
v=I(R(a,b),Q(c,R(a,b)));vp=I(R(a,b),NN(Q(c,R(a,b))))
vp_bridge=cov(R(a,b),dn(Q(c,R(a,b))))
bundle=h.hyp(N(I(v,core)))
nv=h.hyp(N(v));hv=h.hyp(v)
vcore=h.ded(hv,h.mp(h.efq(core),h.mp(nv,hv)))
nnv=h.ded(nv,h.mp(bundle,vcore))
hc=h.hyp(core)
ncore=h.ded(hc,h.mp(bundle,h.mp(h.ax('K',core,v),hc)))
nnvp=h.mp(dnmap(vp_bridge),nnv)
ncorep=h.mp(contra(core_bridge),h.mp(neg_dn_intro(core),ncore))
hvc=h.hyp(I(vp,corep));hvp=h.hyp(vp)
nvp=h.ded(hvp,h.mp(ncorep,h.mp(hvc,hvp)))
out['literal_bundle_to_normalized_translation']=h.ded(bundle,h.ded(hvc,h.mp(nnvp,nvp)))
assert h.form(out['literal_bundle_to_normalized_translation'])==I(N(I(v,core)),N(I(vp,corep)))

# M is a conditional input here; discharging it verifies the finite bridge
# without inserting it, or QS, into the inherited axiom list.
m=I(Q(i,NN(Q(j,z))),NN(Q(j,Q(i,z))))
hm=h.hyp(m)
outer=h.hyp(NN(Q(i,NN(Q(j,z)))))
nnright=h.mp(dnmap(hm),outer)
# DN(DN X) -> DN X is triple-negation elimination at N X.
right=h.mp(neg_dn_elim(N(Q(j,Q(i,z)))),nnright)
last=dnmap(h.normal(j,dn(Q(i,z))))
out['mixed_row_implies_translated_commutation']=h.ded(hm,h.ded(outer,h.mp(last,right)))
assert h.form(out['mixed_row_implies_translated_commutation'])==I(m,I(NN(Q(i,NN(Q(j,z)))),NN(Q(j,NN(Q(i,z))))))

assert h.validate() and all(not h.nodes[k]['open'] for k in out.values())
used=sorted({n['rule'] for n in h.nodes if n['rule'] not in ('mp','gen','hyp')})
assert 'Q_stability' not in used
root=Path(__file__).parent
assert not (root/'bridge-result.json').exists()
result={'status':'FINITE_HILBERT_BRIDGES_PASS','nodes':len(h.nodes),'closed_outputs':{name:{'node':k,'formula':h.form(k)}for name,k in out.items()},'axioms_used':used,'theorem_only_gen':True,'scope':'Finite conditional K/S + rho2/rho6 bridges. Literal transformed bundle is in the explicitly justified N(NN X) normalization. Full co-translation/injectivity and all-natural proof translation are ordinary arguments in proof.md. No QS, old rho4, Lean or machine check.'}
(root/'bridge-result.json').write_text(json.dumps(result,indent=2)+'\n')
(root/'bridge-dag.json').write_text(json.dumps({'nodes':[{**n,'open':sorted(n['open'])} for n in h.nodes],'outputs':out},separators=(',',':'))+'\n')
print(json.dumps({'status':result['status'],'nodes':len(h.nodes),'outputs':len(out),'axioms':used}))
