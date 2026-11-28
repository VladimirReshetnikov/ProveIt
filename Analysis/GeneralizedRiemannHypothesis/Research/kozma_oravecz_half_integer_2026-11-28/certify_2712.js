const S=10n**28n;
const parse=s=>{const neg=s.startsWith("-");if(neg)s=s.slice(1);let [a,b=""]=s.split(".");const x=BigInt(a||"0")*S+BigInt((b+"0".repeat(28)).slice(0,28));return neg?-x:x;};
const I=(a,b=a)=>[parse(a),parse(b)], N=x=>I(String(x));
const min=a=>a.reduce((x,y)=>x<y?x:y),max=a=>a.reduce((x,y)=>x>y?x:y);
const floor=(a,b)=>a/b-(a<0n&&a%b!==0n?1n:0n);
const plus=(a,b)=>[a[0]+b[0],a[1]+b[1]], neg=a=>[-a[1],-a[0]], sub=(a,b)=>plus(a,neg(b));
const mul=(a,b)=>{const v=a.flatMap(x=>b.map(y=>x*y));return [floor(min(v),S),-floor(-max(v),S)];};
const inv=a=>{if(a[1]<0n)return neg(inv(neg(a)));if(a[0]<=0n)throw Error("denominator zero");return [floor(S*S,a[1]),-floor(-S*S,a[0])];};
const div=(a,b)=>mul(a,inv(b)), K=(n,x)=>mul(N(n),x), sum=(...xs)=>xs.reduce(plus,N(0));

const point=a=>[a,a], pos=(x,k)=>{if(x[0]<=0n)throw Error("positive "+k+" "+x)},negative=(x,k)=>pos(neg(x),k);
const zero=N(0),one=N(1);
const evalP=(cs,x)=>cs.reduceRight((y,c)=>plus(mul(y,x),c),zero);
const shift=cs=>[zero,...cs];
function addP(cs,ds){return Array.from({length:Math.max(cs.length,ds.length)},(_,i)=>plus(cs[i]??zero,ds[i]??zero));}
const negP=cs=>cs.map(neg), scaleP=(a,cs)=>cs.map(c=>mul(a,c));
const mulP=(a,b)=>a.reduce((r,c,i)=>addP(r,[...Array(i).fill(zero),...scaleP(c,b)]),[zero]);
const deriv=cs=>cs.slice(1).map((c,i)=>K(i+1,c));
function sequence(first,n){const all=[[one],first];for(let j=2;j<=n;j++)all.push(addP(shift(scaleP(N(2),all[j-1])),negP(all[j-2])));return all;}
const Ts=sequence([zero,one],12), Us=sequence([zero,N(2)],11);
const [T2,T7,T12]=[2,7,12].map(i=>Ts[i]);
const eta=cs=>addP(mulP(deriv(cs),T7),negP(mulP(cs,deriv(T7))));
const E0=eta(T2),E1=eta(T12);
const E=(x,b,d)=>plus(evalP(d?deriv(E0):E0,x),mul(b,evalP(d?deriv(E1):E1,x)));
const R=(x,b)=>div(plus(evalP(T2,x),mul(b,evalP(T12,x))),evalP(T7,x));
const B=I(".46688711936350",".46688711936362");
const ubox=I(".94228289217292",".94228289217299"),vbox=I(".72954822734434",".72954822734442");
function signed(y,s){return s>0?y:neg(y);}
for(const [X,s] of [[ubox,-1],[vbox,1]]){pos(signed(E(X,B,true),s),"curvature");negative(signed(E(point(X[0]),B,false),s),"lower");pos(signed(E(point(X[1]),B,false),s),"upper");}
function find([l,h],b,s){while(h-l>10000n){let m=(l+h)/2n;const w=signed(E(point(m),b,false),s);if(w[0]>0n)h=m;else if(w[1]<0n)l=m;else throw Error("bisection sign");}return [l,h];}
const diff=b=>sub(R(find(ubox,b,-1),b),R(find(vbox,b,1),b));
const z0=diff(point(B[0])),z1=diff(point(B[1]));
negative(z0,"difference lower");pos(z1,"difference upper");
const U=x=>div(evalP(T12,x),evalP(T7,x));
pos(sub(U(ubox),U(vbox)),"difference increasing");
const um=(ubox[0]+ubox[1])/2n, ur=ubox[1]-um;
const lip=div(E(ubox,B,false),mul(evalP(T7,ubox),evalP(T7,ubox)));
const dar=mul(lip,[-ur,ur]);
const A=neg(plus(R(point(um),B),dar)), P=addP(addP(T2,scaleP(A,T7)),scaleP(B,T12));
const X=I(".46362209927",".46362209930");
const value=x=>sum(evalP(T2,x),mul(A,evalP(T7,x)),mul(B,evalP(T12,x)));
negative(value(point(X[0])),"left root bracket");pos(value(point(X[1])),"right root bracket");
pos(evalP(deriv(P),X),"edge derivative");
const mon=x=>[neg(x),one];
const den=[X,ubox,ubox,vbox,vbox].reduce((cs,x)=>mulP(cs,mon(x)),[one]);
function quotient(a,d){const work=a.slice(),q=Array(a.length-d.length+1).fill(zero);for(let i=q.length-1;i>=0;i--){q[i]=work[i+d.length-1];for(let j=0;j<d.length-1;j++)work[i+j]=sub(work[i+j],mul(q[i],d[j]));}return q;}
const Q=quotient(P,den);
const binom=(n,k)=>{let b=1;for(let i=0;i<k;i++)b=b*(n-i)/(i+1);return b;};
let worst=null;
function checkPiece(l,r){
 const n=Q.length-1, width=r-l;
 let c=[zero];for(let i=n;i>=0;i--)c=addP(mulP(c,[point(l),point(width)]),[Q[i]]);
 c=c.slice(0,n+1);
 for(let k=0;k<=n;k++){
  const b=c.slice(0,k+1).reduce((s,x,j)=>plus(s,div(K(binom(k,j),x),N(binom(n,j)))),zero);
  pos(b,"Bernstein");if(!worst||b[0]<worst[0])worst=b;
 }
}
const steps=32n;for(let j=0n;j<steps;j++){let l=X[0]+(S-X[0])*j/steps,r=X[0]+(S-X[0])*(j+1n)/steps;checkPiece(l,r);}
pos(evalP(T7,X),"T7 x");negative(evalP(T7,ubox),"T7 u");pos(evalP(T7,vbox),"T7 v");
pos(sub(U(X),U(ubox)),"slope upper");pos(sub(U(ubox),U(vbox)),"slope lower");
pos(evalP(T2,ubox),"perturb u");pos(evalP(T2,vbox),"perturb v");
const det=m=>m.length===1?m[0][0]:m[0].reduce((a,x,i)=>plus(a,K(i%2?-1:1,mul(x,det(m.slice(1).map(r=>r.filter((_,j)=>i!==j)))))),zero);
const d=det([X,ubox,vbox].map(x=>[1,6,11].map(i=>evalP(Us[i],x))));
negative(d,"odd sine determinant");
const show=x=>x.map(z=>Number(z)/Number(S));
console.log({A:show(A),D0:show(z0),D1:show(z1),edge:show(X),Bernstein:show(worst),oddDet:show(d),length:show(X).map(x=>Math.acos(x)/Math.PI)});

