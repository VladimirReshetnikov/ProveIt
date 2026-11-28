const S=10n**28n;
const parse=s=>{const neg=s.startsWith("-");if(neg)s=s.slice(1);let [a,b=""]=s.split(".");const x=BigInt(a||"0")*S+BigInt((b+"0".repeat(28)).slice(0,28));return neg?-x:x;};
const I=(a,b=a)=>[parse(a),parse(b)], N=x=>I(String(x));
const min=a=>a.reduce((x,y)=>x<y?x:y),max=a=>a.reduce((x,y)=>x>y?x:y);
const floor=(a,b)=>a/b-(a<0n&&a%b!==0n?1n:0n);
const plus=(a,b)=>[a[0]+b[0],a[1]+b[1]], neg=a=>[-a[1],-a[0]], sub=(a,b)=>plus(a,neg(b));
const mul=(a,b)=>{const v=a.flatMap(x=>b.map(y=>x*y));return [floor(min(v),S),-floor(-max(v),S)];};
const inv=a=>{if(a[1]<0n)return neg(inv(neg(a)));if(a[0]<=0n)throw Error("denominator zero");return [floor(S*S,a[1]),-floor(-S*S,a[0])];};
const div=(a,b)=>mul(a,inv(b)), K=(n,x)=>mul(N(n),x), sum=(...xs)=>xs.reduce(plus,N(0));
let factorial=1n; for(let j=2n;j<=90n;j++) factorial*=j;
if((8n**90n)*(10n**25n)>=factorial) throw Error("Taylor remainder bound");
const U0=I(".8436989",".8436992"), V0=I("3.6854923","3.6854926"), B=I("-2.204793","-2.2047928");
function trig(x,odd){
 const t=(x[0]+x[1])/2n, y=[t,t], rad=max([t-x[0],x[1]-t]);
 if(t<-8n*S||t>8n*S)throw Error("input domain");
 const y2=neg(mul(y,y)); let term=odd?y:N(1), ans=term;
 let n=odd?1:0;
 for(;n<=88;n+=2){term=div(mul(term,y2),N((n+1)*(n+2)));ans=plus(ans,term);}
 const err=1000n+rad;return plus(ans,[-err,err]);
}
const sin=x=>trig(x,true),cos=x=>trig(x,false);
const T=(x,b)=>sum(neg(div(x,cos(x))),K(-2,mul(b,sin(x))));
const E=(x,b)=>{const c=cos(x),s=sin(x);return sum(neg(div(plus(c,mul(x,s)),mul(c,c))),K(-2,mul(b,c)));};
const H=(x,b)=>{const c=cos(x),s=sin(x);return sum(neg(div(K(2,s),mul(c,c))),neg(div(mul(x,plus(N(1),mul(s,s))),mul(c,mul(c,c)))),K(2,mul(b,s)));};
const pos=(x,k)=>{if(x[0]<=0n)throw Error("positive "+k+" "+x);};
const negp=(x,k)=>pos(neg(x),k);
const point=x=>[x,x];
negp(H(U0,B),"T second u");pos(H(V0,B),"T second v");
pos(E(point(U0[0]),B),"E u left");negp(E(point(U0[1]),B),"E u right");
negp(E(point(V0[0]),B),"E v left");pos(E(point(V0[1]),B),"E v right");
function find(X,b,sign){let [l,h]=X;while(h-l>10n**11n){const m=(l+h)/2n;let y=E(point(m),b);if(sign<0)y=neg(y);if(y[0]>0n)h=m;else if(y[1]<0n)l=m;else throw Error("indeterminate");}return [l,h];}
function diff(b){return sub(T(find(U0,b,-1),b),T(find(V0,b,1),b));}
const d0=diff(point(B[0])),d1=diff(point(B[1]));
pos(d0,"difference left");negp(d1,"difference right");
const A=T(U0,B);pos(A,"A positive");
const W=I("-1.355137","-1.355132");
const F=x=>sum(x,mul(A,cos(x)),mul(B,sin(K(2,x))));
negp(F(point(W[0])),"F edge low");pos(F(point(W[1])),"F edge high");
pos(sum(N(1),neg(mul(A,sin(W))),K(2,mul(B,cos(K(2,W))))),"F edge derivative");
pos(sub(sin(V0),sin(W)),"dual left");pos(sub(sin(U0),sin(V0)),"dual right");
const show=x=>x.map(y=>Number(y)/Number(S));
console.log({A:show(A),d0:show(d0),d1:show(d1),edge:show(W),sin:[W,V0,U0].map(x=>show(sin(x))),Ederivatives:[show(H(U0,B)),show(H(V0,B))]});

const forcing=x=>sum(neg(mul(A,mul(x,sin(x)))),mul(B,mul(x,cos(K(2,x)))));
const cu=cos(U0),cv=cos(V0),su=sin(K(2,U0)),sv=sin(K(2,V0));
const det=sub(mul(cu,sv),mul(cv,su));
const dA=div(sub(mul(forcing(V0),su),mul(forcing(U0),sv)),det);
const dB=div(sub(mul(cv,forcing(U0)),mul(cu,forcing(V0))),det);
const slope=sum(N(1),neg(mul(A,sin(W))),K(2,mul(B,cos(K(2,W)))));
const edgeSlope=neg(div(sum(mul(dA,cos(W)),mul(dB,sin(K(2,W))),forcing(W)),slope));
pos(sub(edgeSlope,N(".7858")),"edge derivative lower");pos(sub(N(".7861"),edgeSlope),"edge derivative upper");
console.log({edgeSlope:show(edgeSlope)});

