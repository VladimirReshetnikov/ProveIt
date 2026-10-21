#!/usr/bin/env python3
"""One owned combined producer/equality pilot, without grammar enumeration."""
from pathlib import Path
import hashlib,json,sys,time
D=Path(__file__).resolve().parent/'shared_recolored_equality';D.mkdir(exist_ok=True);ROOT=D.parent.parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
P=A.P
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sp=ROOT/'latest218_baseline/candidate-k218/sites218.json';tp=ROOT/'latest218_baseline/candidate-k218/k218.native.tm';sites=json.loads(sp.read_text());old=P.tree(sites);E=A.at(old,'11110')
def rename(n):
 if P.leaf(n):return(n[0],{5:3,6:5}.get(n[1],n[1]))if n[0]in('CI','CD')else n
 return(rename(n[0]),rename(n[1]))
E35=rename(E);replaced=0
def all_e(n):
 global replaced
 if n==E:replaced+=1;return E35
 if P.leaf(n):return n
 return(all_e(n[0]),all_e(n[1]))
new=all_e(old);assert replaced==4
edits=[]
for i in[4580,4598,4706]:
 path=sites[i][0];assert A.at(new,path)==('CI',6);new=A.replace(new,path,('CI',3));edits.append(dict(source_index=i,path=path,old=['CI',6],new=['CI',3]))
dup_path=sites[4563][0][:-1];dup=A.at(new,dup_path);assert dup==(('CD',3),(('CI',7),(('CI',6),('CC',3))))
restore=A.at(old,sites[20][0][:-1]);assert restore==(('CD',6),(('CI',3),('CC',2)))
assert A.boundary(dup)==A.boundary(restore)==(0,0,False)
new=A.replace(new,dup_path,(dup,restore));ns=A.flatten(new);outsource=D/'sites.json';outsource.write_bytes(A.compact(ns));assert len(ns)==4747
before={(o,a,p[-1])for p,o,a in sites};after={(o,a,p[-1])for p,o,a in ns}
result=dict(status='RAW_ALLOCATION_PENDING',baseline_table_sha256=H(tp),baseline_source_sha256=H(sp),source_sha256=H(outsource),source_nodes=len(P.nodes(new))+len({(o,a)for p,o,a in ns}),primitive_occurrences=len(ns),equality_calls=replaced,producer_edits=edits,first_producer_path=dup_path,restoration_ast=restore,restoration_already_existing=True,new_leaf_interfaces=sorted(after-before,key=str),proof='For arbitrary cacheb, selectorc and other registers, withR6=0: the first existing duplicate clearsR3 intoR6/R7; existingT63 then restoresc toR3 while clearingR6. E35 clearsR3/R5 and has the same equality exit as the old E56. It leaves the savedR7 copy untouched. At the other three producersR3=R6=0, so directCI6→CI3 retargeting followed byE35 has the same endpoint and equality exit as the old producer/E56. In particular NIP halts exactly at cache1. No consistency assumption is used.',scope='One exact combined source candidate. Source arithmetic contracts and raw allocation do not certify new right-childCD5 engine semantics, whole-machine runtime or blank initialization.')
beg=time.monotonic()
try:
 T,price=P.compile(A.R.table(tp),old,new);outtable=D/'raw.native.tm';outtable.write_bytes(P.M.enc(T));result.update(status='UNPROVED_RAW_COMPILER_PRICE',raw_price=price,raw_table_sha256=H(outtable))
except Exception as e:result.update(status='ALLOCATOR_FAILURE_NOT_A_STATE_PRICE',error=repr(e))
result['seconds']=time.monotonic()-beg;(D/'PRICE.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
