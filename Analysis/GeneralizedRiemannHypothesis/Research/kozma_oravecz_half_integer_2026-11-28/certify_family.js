"use strict";
// Rigorous parameter cover; floating point is used ONLY to propose
// grid points and a preconditioner. All assertions use BigInt intervals.
const fs=require("node:fs");
const minus=process.argv.includes("--minus"), plus=process.argv.includes("--plus");
if(minus===plus)throw Error("choose exactly one of --minus, --plus");
const sign=minus?-1:1;
const P=10n**23n;
const fl=(a,b)=>a/b-(a<0n&&a%b!==0n?1n:0n);
const cp=(a,b)=>-fl(-a,b);
const abs=a=>a<0n?-a:a;
const min=a=>a.reduce((a,b)=>a<b?a:b), max=a=>a.reduce((a,b)=>a>b?a:b);
const N=n=>{const p=BigInt(n)*P;return[p,p];};
const pt=n=>[n,n], I=(a,b)=>[a,b];
const divn=(x,n)=>[fl(x[0],BigInt(n)),cp(x[1],BigInt(n))];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]], neg=a=>[-a[1],-a[0]];
const sub=(a,b)=>add(a,neg(b));
const mul=(a,b)=>{const v=a.flatMap(x=>b.map(y=>x*y));return [fl(min(v),P),cp(max(v),P)];};
const inv=a=>{if(a[1]<0n)return neg(inv(neg(a)));if(a[0]<=0n)throw Error("division by zero");return [fl(P*P,a[1]),cp(P*P,a[0])];};
const div=(a,b)=>mul(a,inv(b)), K=(n,x)=>mul(N(n),x), sum=(...xs)=>xs.reduce(add,N(0));
const mid=x=>(x[0]+x[1])/2n;
const rad=(x,m)=>max([m-x[0],x[1]-m]);
const widen=(x,w)=>[x[0]-w,x[1]+w];
const est=x=>Number(x)/Number(P);
const rat=(a,b)=>divn(N(a),b);
const dot=(a,b)=>sum(...a.map((x,i)=>mul(x,b[i])));
const matmul=(A,B)=>A.map(r=>B[0].map((_,j)=>dot(r,B.map(row=>row[j]))));
const mag=x=>max(x.map(abs));
const positive=(x,msg)=>{if(x[0]<=0n)throw Error(msg);};
const negative=(x,msg)=>positive(neg(x),msg);
const qfloat=x=>{if(!Number.isFinite(x)||Math.abs(x)>1e4)throw Error("unusable proposal");return BigInt(Math.round(x*1e12))*(P/10n**12n);};
const fac=n=>{let f=1n;for(let i=2n;i<=n;i++)f*=i;return f;};
if(3n**44n*P>=fac(44n))throw Error("Taylor bound");
function series(x,kind){
 const y=neg(mul(x,x));let term=kind===1?x:N(1),r=term;
 // cos degree 42, sin degree 43, sinc degree 42.
 for(let j=1;j<=21;j++){
  const n=2*j+(kind===0?0:1);
  term=divn(mul(term,y),n*(n-1)); r=add(r,term);
 }
 return widen(r,1n);
}
function sc(x){
 const m=mid(x),d=rad(x,m),y=divn(pt(m),8);
 if(mag(y)>3n*P)throw Error("angle range");
 let s=series(y,1),c=series(y,0);
 for(let j=0;j<3;j++)[s,c]=[K(2,mul(s,c)),sub(mul(c,c),mul(s,s))];
 return [widen(s,d),widen(c,d)];
}
function sinc(x){
 const m=mid(x);
 if(abs(m)>3n*P)throw Error("sinc range");
 return widen(series(pt(m),2),cp(rad(x,m),2n));
}
function basis(e,z){
 const p=add(N(1),e),q=add(N(2),e),w=mul(e,z);
 const [a,b]=sc(w),[c,d]=sc(mul(p,z)),[f,g]=sc(mul(q,z)), C=add(d,K(sign,c));
 return [[mul(z,sinc(w)),C,g],
         [b,mul(p,sub(K(sign,d),c)),neg(mul(q,f))],
         [neg(mul(e,a)),neg(mul(mul(p,p),C)),neg(mul(mul(q,q),g))]];
}
function residual(e,z,wantJacobian){
 const [a,b,u,v,x]=z, coeff=[N(1),a,b], [U,V,X]=[u,v,x].map(y=>basis(e,y));
 const f=[U[0],V[0],U[1],V[1],X[0]].map(r=>dot(coeff,r));
 if(!wantJacobian)return f;
 const z0=N(0);
 return [[U[0][1],U[0][2],f[2],z0,z0],
         [V[0][1],V[0][2],z0,f[3],z0],
         [U[1][1],U[1][2],dot(coeff,U[2]),z0,z0],
         [V[1][1],V[1][2],z0,dot(coeff,V[2]),z0],
         [X[0][1],X[0][2],z0,z0,dot(coeff,X[1])]];
}
function approxInverse(M){
 const a=M.map((r,i)=>[...r.map(x=>est(mid(x))),...M.map((_,j)=>i===j?1:0)]);
 for(let i=0;i<a.length;i++){
  let p=i;for(let j=i+1;j<a.length;j++)if(Math.abs(a[j][i])>Math.abs(a[p][i]))p=j;
  [a[i],a[p]]=[a[p],a[i]];
  const q=a[i][i];a[i]=a[i].map(x=>x/q);
  for(let j=0;j<a.length;j++)if(i!==j){const q=a[j][i];a[j]=a[j].map((x,k)=>x-q*a[i][k]);}
 }
 return a.map(r=>r.slice(M.length).map(x=>pt(qfloat(x))));
}
let nodes=0, leaf=0, tests=0, deepest=0;
function propose(E){
 const guess=require("./guess.js");
 const em=mid(E);
 const [u,v,x,a,b]=guess(est(em),sign);
 const center=[a,b,u,v,x].map(qfloat), point=center.map(pt);
 const R=approxInverse(residual(pt(em),point,true));
 const f=residual(E,point,false);
 const rf=R.map(r=>dot(r,f));
 // Use a common radius; the enclosure must be independently verified.
 const r=3n*max([P/10n**11n,...rf.map(mag)]);
 return {E,center,R,r};
}
function verify({E,center,R,r}){
 if(E[0]<0n||E[0]>=E[1]||r<=0n||center.length!==5||R.length!==5||
    R.some(row=>row.length!==5||row.some(t=>t.length!==2||t[0]!==t[1])))
   throw Error("malformed certificate");
 const rf=R.map(row=>dot(row,residual(E,center.map(pt),false)));
 const box=center.map(c=>widen(pt(c),r));
 const IJ=matmul(R,residual(E,box,true)).map((row,i)=>row.map((t,j)=>sub(N(i===j?1:0),t)));
 IJ.forEach((row,i)=>{
   const q=row.reduce((s,t)=>s+mag(t),0n);
   if(q>=P||mag(rf[i])+cp(q*r,P)>=r)throw Error("contraction");
 });
 const [A,B,U,V,X]=box, coeff=[N(1),A,B];
 if(X[0]<=-2n*P||X[1]>=0n||U[0]<=0n||U[1]>=V[0]||100n*V[1]*E[1]>=157n*P*P)throw Error("root order");
 if(3n*mag(A)+2n*mag(B)>=rat(126,11)[0])throw Error("tail");
 const evalF=(s,order)=>dot(coeff,basis(E,s)[order]);
 const dh=P/9n;
 const XX=widen(X,dh),UU=widen(U,dh),VV=widen(V,dh);
 positive(evalF(XX,1),"endpoint derivative");
 positive(evalF(UU,2),"first minimum");
 positive(evalF(VV,2),"second minimum");
 const end=E[0]===0n?9n*P:min([9n*P,cp(11n*P*P,7n*E[0])]);
 if(!(XX[1]<UU[0]&&UU[1]<VV[0]&&VV[1]<end))throw Error("region order");
 function cover(l,h,depth){
  tests++;if(evalF(I(l,h),0)[0]>0n)return;
  if(depth>=15)throw Error("positive cover");
  const m=(l+h)/2n;cover(l,m,depth+1);cover(m,h,depth+1);
 }
 for(const [l,h] of [[XX[1],UU[0]],[UU[1],VV[0]],[VV[1],end]])cover(l,h,0);
 const rows=[X,U,V].map(z=>basis(E,z)[0].slice(1));
 const minors=rows.map((_,i)=>{
   const [a,b]=rows[(i+1)%3], [c,d]=rows[(i+2)%3];
   return sub(mul(a,d),mul(b,c));
 });
 if(!minors.every(t=>t[0]>0n)&&!minors.every(t=>t[1]<0n))throw Error("dual signs");
 const p=add(N(1),E),q=add(N(2),E);
 const [aa,bb,cc]=[X,U,V].map(z=>{
   const [s,c]=sc(mul(p,z));
   return [sc(mul(E,z))[1],sub(s,K(sign,c)),sc(mul(q,z))[0]];
 });
 const dd=(i,j)=>sub(mul(bb[i],cc[j]),mul(bb[j],cc[i]));
 positive(K(sign,sum(mul(aa[0],dd(1,2)),neg(mul(aa[1],dd(0,2))),mul(aa[2],dd(0,1)))),"odd determinant");
}
const witnesses=[];
function sweep(a,b,d){
 nodes++;try{const w=propose([a,b]);verify(w);witnesses.push(w);
   leaf++;deepest=Math.max(d,deepest);return;}
 catch(e){
  if(d>=16)throw Error("near "+est(a)+" : "+e.message);
  const m=(a+b)/2n;sweep(a,m,d+1);sweep(m,b,d+1);
 }
}
const filepath=require("node:path").join(__dirname,minus?"minus.json":"plus.json");
const top=(minus?rat(2,5):rat(2,7))[1];
if(process.argv.includes("--emit")){
 sweep(0n,top,0);
 fs.writeFileSync(filepath,JSON.stringify(witnesses,(_,v)=>typeof v==="bigint"?String(v):v));
 console.log({status:"cover generated",nodes,leaf,deepest,tests});
}else{
 const W=JSON.parse(fs.readFileSync(filepath,"utf8"),(_,v)=>typeof v==="string"?BigInt(v):v);
 let edge=0n;
 for(const w of W){
   if(w.E[0]!==edge)throw Error("coverage gap or order mismatch");
   verify(w);
   edge=w.E[1];
 }
 if(edge!==top)throw Error("coverage endpoint");
 console.log({status:"all cells certified",cells:W.length,compactSignTests:tests});
}
