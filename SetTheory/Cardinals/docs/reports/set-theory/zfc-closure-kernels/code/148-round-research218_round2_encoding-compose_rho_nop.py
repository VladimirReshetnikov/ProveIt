"""Owned literal AST composition; supplied programs are never imported."""
from pathlib import Path
import json,sys,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_encoding'));import price_sources as P
B=ROOT/'latest219_baseline/candidate-k219';N=ROOT/'research218_round2_review/inert/ZFC_218_State_Search_2026-10-20/machines'
def dump(n,x):(OUT/n).write_text(json.dumps(x,indent=2)+'\n')
def flatten(t,p=''):
 if P.leaf(t):return[[p,*t]]
 return flatten(t[0],p+'0')+flatten(t[1],p+'1')
def subst(t,a,b):
 if t==a:return b,1
 if P.leaf(t):return t,0
 l,c=subst(t[0],a,b);r,d=subst(t[1],a,b);return(l,r),c+d

def main():
 bt=P.D.table(B/'k219.native.tm');bs=P.tree(json.load(open(B/'sites219.json')));rt=P.D.table(N/'rho6_219/native.tm');rs=P.tree(json.load(open(N/'rho6_219/sites.json')));nt=P.D.table(N/'nop219/native.tm');ns=P.tree(json.load(open(N/'nop219/sites.json')))
 pins={str(p):P.D.H(p.read_bytes())for p in[B/'k219.native.tm',B/'sites219.json',N/'rho6_219/native.tm',N/'rho6_219/sites.json',N/'nop219/native.tm',N/'nop219/sites.json']}
 bg,bp,_=P.allocation(bt,bs);rg,rp,_=P.allocation(rt,rs);ng,np,_=P.allocation(nt,ns);assert len(bg[206])==len(rg[206])==len(ng[206])==1
 old=next(iter(bg[206]));new=next(iter(rg[206]));assert next(iter(ng[206]))==old
 rebuilt,count=subst(bs,old,new);assert count==1 and rebuilt==rs
 combined,count=subst(ns,old,new);assert count==1
 table,receipt=P.compile(nt,ns,combined);patch={k:a for k,a in rt.items()if bt[k]!=a};assert set(patch)=={(199,1),(206,0)};assert all(nt[k]==bt[k]for k in patch)
 union=nt|patch;assert table==union
 sites=flatten(combined);data=(json.dumps(sites,indent=2)+'\n').encode();out=OUT/'rho_nop_combined';out.mkdir(exist_ok=True);(out/'sites.json').write_bytes(data);raw=P.M.enc(table);(out/'native.tm').write_bytes(raw)
 receipt.update(status='EXACT_LITERAL_SOURCE_COMPOSITION_AND_PREFIX_BINDING',source_sha256=P.D.H(data),native_sha256=P.D.H(raw),source_leaves=len(sites),subtree_occurrences=count,transported_role=206,old_role_path=[p for p,q in bp.items()if q==206],new_role_path=[p for p,q in np.items()if q==206],input_pins=pins,source_obligation='Rho6 reparameterization affects the same unique230-leaf subtree inside the nop source. Full mathematical calibration and whole-machine runtime/startup remain separate obligations. No reduction below219 is obtained.')
 dump('RHO_NOP_COMPOSITION.json',receipt);print(json.dumps({k:v for k,v in receipt.items()if k not in('input_pins',)}),flush=True)
if __name__=='__main__':main()
