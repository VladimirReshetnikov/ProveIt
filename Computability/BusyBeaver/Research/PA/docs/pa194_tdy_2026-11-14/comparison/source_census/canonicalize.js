
function parseTM(text) {
 const rows=new Map();let declared=null;
 for(const line of text.split(/\r?\n/)){
  const s=line.trim();if(!s)continue;
  if(s.startsWith("#")){const m=s.match(/\bstart\s*(\d+)/);if(m&&declared===null)declared=Number(m[1]);continue;}
  const t=s.split(/\s+/);if(t.length!==5)throw Error("bad fields");
  const [q,b,w,d,n]=[Number(t[0]),Number(t[1]),Number(t[2]),t[3],Number(t[4])];
  if(!Number.isInteger(q)||!Number.isInteger(n)||![0,1].includes(b)||![0,1].includes(w)||!["L","R"].includes(d)||rows.has(q+":"+b))throw Error("bad row");
  rows.set(q+":"+b,[w,d,n]);
 }
 const states=[...new Set([...rows.keys()].map(x=>Number(x.split(":")[0])))].sort((a,b)=>a-b),set=new Set(states);
 if(states.some(q=>![0,1].every(b=>rows.has(q+":"+b))))throw Error("incomplete");
 return {rows,states,set,start:declared!==null?declared:states.every((q,i)=>q===i)?0:null,declared};
}
function canonRoot(m,start,mirror=false,flip=false,loose=false){
 const ids=new Map([[start,0]]),order=[start],out=[];
 for(let i=0;i<order.length;i++){const q=order[i];for(let b=0;b<2;b++){let [w,d,n]=m.rows.get(q+":"+(b^(flip?1:0)));if(flip)w^=1;if(mirror)d=d==="L"?"R":"L";if(m.set.has(n)){if(!ids.has(n)){ids.set(n,ids.size);order.push(n);}out.push([w,d,ids.get(n)]);}else out.push(loose?[0,"R",-1]:[w,d,-1]);}}
 return {n:order.length,text:JSON.stringify(out)};
}
function canonTable(m,extended=false){let best=null,most=0;for(const q of m.states){for(const [mi,fl] of (extended?[[false,false],[true,false],[false,true],[true,true]]:[[false,false]])){const c=canonRoot(m,q,mi,fl);if(c.n>most){most=c.n;best=c.text;}else if(c.n===most&&(best===null||c.text<best))best=c.text;}}return {n:most,text:best};}


function sha256Ascii(ascii) {
 let rightRotate=(value,amount)=>(value>>>amount)|(value<<(32-amount));
 let mathPow=Math.pow,maxWord=mathPow(2,32),lengthProperty='length',i,j,result='',words=[],asciiBitLength=ascii[lengthProperty]*8;
 let hash=[],k=[],primeCounter=0,isComposite={};
 for(let candidate=2;primeCounter<64;candidate++){
  if(!isComposite[candidate]){
   for(i=0;i<313;i+=candidate)isComposite[i]=candidate;
   hash[primeCounter]=(mathPow(candidate,.5)*maxWord)|0;
   k[primeCounter++]=(mathPow(candidate,1/3)*maxWord)|0;
  }
 }
 ascii+='\x80';while(ascii[lengthProperty]%64-56)ascii+='\x00';
 for(i=0;i<ascii[lengthProperty];i++){j=ascii.charCodeAt(i);if(j>>8)throw Error("nonbyte");words[i>>2]|=j<<((3-i)%4)*8;}
 words[words[lengthProperty]]=(asciiBitLength/maxWord)|0;words[words[lengthProperty]]=asciiBitLength;
 for(j=0;j<words[lengthProperty];){
  let w=words.slice(j,j+=16),oldHash=hash;hash=hash.slice(0,8);
  for(i=0;i<64;i++){
   let w15=w[i-15],w2=w[i-2],a=hash[0],e=hash[4];
   let temp1=hash[7]+(rightRotate(e,6)^rightRotate(e,11)^rightRotate(e,25))+((e&hash[5])^((~e)&hash[6]))+k[i]+(w[i]=(i<16)?w[i]:((w[i-16]+(rightRotate(w15,7)^rightRotate(w15,18)^(w15>>>3))+w[i-7]+(rightRotate(w2,17)^rightRotate(w2,19)^(w2>>>10)))|0));
   let temp2=(rightRotate(a,2)^rightRotate(a,13)^rightRotate(a,22))+((a&hash[1])^(a&hash[2])^(hash[1]&hash[2]));
   hash=[(temp1+temp2)|0].concat(hash);hash[4]=(hash[4]+temp1)|0;hash.pop();
  }
  for(i=0;i<8;i++)hash[i]=(hash[i]+oldHash[i])|0;
 }
 for(i=0;i<8;i++)for(j=3;j+1;j--){let b=(hash[i]>>(j*8))&255;result+=((b<16)?'0':'')+b.toString(16);}
 return result;
}
function csvParse(text) {
 const rows=[];let r=[],v="",q=false;
 for(let i=0;i<text.length;i++){const c=text[i];if(q){if(c==='"'){if(text[i+1]==='"'){v+='"';i++;}else q=false;}else v+=c;}else if(c==='"')q=true;else if(c===','){r.push(v);v="";}else if(c==='\n'){r.push(v.replace(/\r$/,""));rows.push(r);r=[];v="";}else v+=c;}
 if(v||r.length){r.push(v);rows.push(r);}
 const keys=rows.shift();return rows.filter(r=>r.length>1).map(r=>Object.fromEntries(r.map((v,i)=>[keys[i],v])));
}
