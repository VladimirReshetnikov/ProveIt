const S=10n**24n;
const parse=s=>{const neg=s.startsWith("-");if(neg)s=s.slice(1);let [a,b=""]=s.split(".");const x=BigInt(a||"0")*S+BigInt((b+"0".repeat(24)).slice(0,24));return neg?-x:x;};
const I=(a,b=a)=>[parse(a),parse(b)], N=x=>I(String(x)), min=a=>a.reduce((x,y)=>x<y?x:y),max=a=>a.reduce((x,y)=>x>y?x:y);
const floor=(a,b)=>a/b-(a<0n&&a%b!==0n?1n:0n);
const plus=(a,b)=>[a[0]+b[0],a[1]+b[1]], neg=a=>[-a[1],-a[0]], sub=(a,b)=>plus(a,neg(b));
const mul=(a,b)=>{const v=a.flatMap(x=>b.map(y=>x*y));return [floor(min(v),S),-floor(-max(v),S)];};
const inv=a=>{if(a[0]<=0n)throw Error("nonpositive denominator");return [floor(S*S,a[1]),-floor(-S*S,a[0])];};
const evalP=(cs,x)=>cs.reduceRight((y,c)=>plus(mul(y,x),c),[0n,0n]);
const P=(cs,x)=>evalP(cs.map(N),x), K=(n,x)=>mul(N(n),x), sum=(...xs)=>xs.reduce(plus,N(0));
const U=x=>P([-7,0,56,0,-112,0,64],x), V=x=>plus(P([0,-8,0,8],x),inv(x));
const F=(x,b)=>sum(mul(b,P([0,112,0,-448,0,384],x)),P([-8,0,24],x),neg(inv(mul(x,x))));
const derivative=(x,b)=>sum(mul(b,P([112,0,-1344,0,1920],x)),K(48,x),K(2,inv(mul(x,mul(x,x)))));
const B=I(".9208242456520",".9208242456522");
const ubox=I(".2680823592348",".2680823592351"),vbox=I(".8545996486673",".8545996486676");
const pos=(x,k)=>{if(x[0]<=0n)throw Error("positive "+k+" "+x)};
const negative=(x,k)=>pos(neg(x),k);
const ending=(F,box,b)=>{negative(F([box[0],box[0]],b),"left");pos(F([box[1],box[1]],b),"right");};
for(const X of [ubox,vbox]){pos(derivative(X,B),"derivative");ending(F,X,B);}
function find(X,b){let [l,h]=X;while(h-l>100000n){const m=(l+h)/2n,f=F([m,m],b);if(f[0]>0n)h=m;else if(f[1]<0n)l=m;else throw Error("indeterminate");}return [l,h];}
function d(b){const x=find(ubox,b),y=find(vbox,b);return sum(mul(b,sub(U(y),U(x))),sub(V(y),V(x)));}
const dl=d([B[0],B[0]]),dh=d([B[1],B[1]]);negative(dl,"delta low");pos(dh,"delta high");
pos(sub(U(vbox),U(ubox)),"delta derivative");
const su=plus(ubox,vbox), pr=mul(ubox,vbox), w=plus(mul(su,su),K(2,pr));
const c3=K(64,B),c2=K(2,mul(su,c3)),c1=sum(K(-112,B),K(2,mul(su,c2)),neg(mul(w,c3))),c0=sum(N(8),K(2,mul(su,c1)),neg(mul(w,c2)),K(2,mul(mul(su,pr),c3)));
const G=[c0,c1,c2,c3],xbox=I("-.363908019","-.363908014");
ending((x)=>evalP(G,x),xbox);
const xL=[xbox[0],xbox[0]];
pos(c3,"cubic leading");
pos(evalP([c1,K(2,c2),K(3,c3)],xL),"G prime left");
pos(evalP([K(2,c2),K(6,c3)],xL),"G second derivative left");
pos(sub(U(xbox),U(ubox)),"dual left");
pos(sub(U(vbox),U(xbox)),"dual right");
const show=x=>x.map(y=>Number(y)/Number(S));
console.log({dl:show(dl),dh:show(dh),derivatives:[show(derivative(ubox,B)),show(derivative(vbox,B))],coefs:G.map(show),root:show(xbox),Ug:[ubox,xbox,vbox].map(x=>show(U(x))),length:show(xbox).map(x=>Math.acos(x)/Math.PI)});

