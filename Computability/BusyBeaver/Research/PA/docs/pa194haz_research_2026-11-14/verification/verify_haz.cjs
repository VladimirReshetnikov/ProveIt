// Independently ported symbolic resolver/runtime. Arithmetic-block contracts are inherited.
function verifyHAZ(baselineText, grammarJSON, programText) {

  const adEdits=[["17 1 0 R 32\n","17 1 0 R 48\n"],["144 1 0 R 48\n","144 1 0 R 32\n"],["161 1 0 R 32\n","161 1 0 R 48\n"]];
  for(const [before,after] of adEdits){if(baselineText.split(before).length!==2)throw Error("A/D patch precondition");baselineText=baselineText.replace(before,after);}

  function assert(v,m){if(!v)throw Error(m)}
  const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
  const BIT=[["b",0],["b",1]],PLAIN=["x","none",-1];
  const SK=[51,36,25,48,32,33,22,55,60],PHYSICAL=[6,2,0,3,4,7,8,5,1];
  const SKMAP=Object.fromEntries(SK.map((q,i)=>[q,i]));
  const baseRows={};
  for(const line of baselineText.trim().split("\n")){
    const [q,b,w,d,n]=line.trim().split(/\s+/);
    baseRows[q]??=[];baseRows[q][+b]=[+w,d==="R",+n];
  }
  const nodes={};
  for(const line of programText.split("\n")){
    const m=line.match(/^def (\w+) : Tree := \.node (.*)/);
    if(!m)continue;
    const cs=[...m[2].matchAll(/\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b/g)]
      .map(x=>x[3]||["leaf",x[1],x[2]===undefined?null:+x[2]]);
    assert(cs.length===2,"two node children");nodes[m[1]]=cs;
  }
  function grammar(x){
    if(Array.isArray(x))return x;
    return grammarJSON.rules[x]?grammarJSON.rules[x].map(grammar):x;
  }
  const ax=grammar(grammarJSON.root);
  function norm(xs,left=false){
    const out=[];
    for(let x of xs){
      if(x[0]==="b")x=["r",x[1],0,1];
      if(x[0]==="r"&&x[2]===0&&x[3]===0)continue;
      const y=out[out.length-1];
      if(y&&x[0]==="r"&&y[0]==="r"&&x[1]===y[1])
        out[out.length-1]=["r",x[1],x[2]+y[2],x[3]+y[3]];
      else out.push(x);
    }
    if(left&&out.length&&out.at(-1)[0]==="r"&&out.at(-1)[1]===0)out.pop();
    return out;
  }
  const canonical=s=>[s[0],s[1],norm(s[2],true),norm(s[3])];
  const matches=(s,t)=>s[0]===t[0]&&s[1]===t[1]&&eq(norm(s[2],true),t[2])&&eq(norm(s[3]),t[3]);
  const frame=(p,extra=0,effect=PLAIN)=>[84,false,[BIT[1]],[...p.map(b=>BIT[b]),["r",0,1,48+extra-p.length],BIT[1],effect]];
  function source(){
    const sites=[];
    function walk(t,p){
      if(typeof t==="string")return walk(t==="x67"?ax:nodes[t],p);
      if(t[0]==="leaf"){sites.push([p,t[1],t[2]]);return;}
      walk(t[0],[...p,0]);walk(t[1],[...p,1]);
    }
    walk("node172",[]);
    const byPath=new Map(sites.map(([p],i)=>[p.join(""),i]));
    function locate(p){
      const k=p.join("");if(byPath.has(k))return byPath.get(k);
      for(let i=0;i<sites.length;i++){
        const q=sites[i][0].join("");
        if(q.startsWith(k)||(k.startsWith(q)&&!k.slice(q.length).includes("1")))return i;
      }
      throw Error("address not located");
    }
    function after(p){
      p=p.slice();
      for(let i=p.length-1;i>=0;i--)if(p[i]===0){p[i]=1;return locate(p.slice(0,i+1));}
      throw Error("program exit");
    }
    function cut(p,b,k){
      for(let i=p.length-1;i>=0;i--)if(p[i]===b&&!--k)return p.slice(0,i);
      throw Error("invalid control depth");
    }
    const ins=sites.map(([p,op,a])=>{
      if(op==="inc")return ["inc",a,after(p)];
      if(op==="dec")return ["dec",a,after(cut(p,0,1)),after(p)];
      if(op==="breakTo")return ["jump",after(cut(p,0,a))];
      if(op==="continueTo")return ["jump",locate(cut(p,1,a))];
      if(op==="halt")return ["halt"];
      throw Error(op);
    });
    const contracts=[];
    for(let i=0;i<ins.length;i++){
      const c=ins[i],s=frame(sites[i][0]);
      if(c[0]==="inc")contracts.push([i,null,s,canonical(frame(sites[c[2]][0],0,["x","inc",PHYSICAL[c[1]]]))]);
      else if(c[0]==="dec"){
        contracts.push([i,[PHYSICAL[c[1]],true],s,canonical(frame(sites[c[2]][0]))]);
        contracts.push([i,[PHYSICAL[c[1]],false],s,canonical(frame(sites[c[3]][0],1,["x","dec",PHYSICAL[c[1]]]))]);
      }else if(c[0]==="jump")contracts.push([i,null,s,canonical(frame(sites[c[1]][0]))]);
      else contracts.push([i,null,s,null]);
    }
    return {sites,ins,contracts};
  }
  function oracle(q,br,x){
    const [,kind,r]=x;
    if(kind==="none"&&Object.hasOwn(SKMAP,q)){
      const rr=SKMAP[q];return [rr===0?1:3,["x","mark",rr],false];
    }
    if(kind==="mark"&&r<9){
      if(q===64)return [40,["x","inc",r],false];
      if(q===0&&br!==null&&br[0]===r)
        return br[1]?[97,PLAIN,false]:[40,["x","dec",r],true];
    }
    return null;
  }
  function step(rows,br,s){
    const [q,onl,l,r]=s;
    if(onl){
      if(!l.length)return [[q,false,[],[BIT[0],...r]],false];
      const [x,...tail]=l;
      if(x[0]==="b")return [[q,false,tail,[x,...r]],false];
      if(x[0]==="r"){
        const [,b,a,c]=x,act=rows[q]?.[b];
        if(act&&!act[1]&&act[2]===q)return [[q,true,tail,[["r",act[0],a,c],...r]],false];
        if(c>0)return [[q,true,[BIT[b],["r",b,a,c-1],...tail],r],false];
        if(a===0)return [[q,true,tail,r],false];
      }return null;
    }
    if(!r.length)return null;
    const [x,...tail]=r;
    if(x[0]==="b"){
      const act=rows[q]?.[x[1]];if(!act)return null;
      const [w,d,n]=act;
      return [d?[n,false,[BIT[w],...l],tail]:[n,true,l,[BIT[w],...tail]],true];
    }
    if(x[0]==="r"){
      const [,b,a,c]=x,act=rows[q]?.[b];
      if(act&&act[1]&&act[2]===q)return [[q,false,[["r",act[0],a,c],...l],tail],false];
      if(c>0)return [[q,false,l,[BIT[b],["r",b,a,c-1],...tail]],false];
      if(a===0)return [[q,false,l,tail],false];
      return null;
    }
    if(tail.length)return null;
    const oc=oracle(q,br,x);
    if(oc){const [n,x2,extra]=oc;return [[n,true,extra?[BIT[1],...l]:l,[x2]],false];}
    const act=rows[q]?.[0];
    if(act&&act[0]===0&&!act[1])return [[act[2],true,l,r],true];
    return null;
  }
  function validate(rows,cs){
    let total=0,max=0;
    for(const [site,br,start,target] of cs){
      let s=start,moved=false,result=null;
      for(let k=0;k<1024;k++){
        if(moved&&(target===null?s[0]===254:matches(s,target))){result=k;break;}
        const nxt=step(rows,br,s);assert(nxt!==null,"symbolic block: "+site);
        [s]=nxt;moved||=nxt[1];
      }
      assert(result!==null,"symbolic timeout: "+site);total+=result;max=Math.max(max,result);
    }
    return {ok:true,contracts:cs.length,max_steps:max,total_steps:total};
  }
  const baseline=source();
  assert(baseline.sites.length===3673,"baseline sites");
  const baseCheck=validate(baseRows,baseline.contracts);
  assert(eq(baseCheck,{ok:true,contracts:4780,max_steps:497,total_steps:1479348}),"baseline verification receipt");
  const hRows=JSON.parse(JSON.stringify(baseRows));
  assert(eq(hRows[164][1],[1,true,98]),"baseline edge");
  hRows[164][1]=[1,true,130];
  assert(eq(hRows[2066][1],[0,false,302]),"baseline final AX edge");
  hRows[2066][1]=[1,true,21];
  assert(eq(nodes.node163,["node6","node55"]),"baseline source edge");
  nodes.node163=["node6","node147"];
  const lastRule=grammarJSON.rules.g61;
  assert(eq(lastRule,["node150",["leaf","breakTo",1]]),"emitter end");
  function replaceFinal(t){if(Array.isArray(t)&&t.length===2&&t[0]==="node150"&&eq(t[1],["leaf","breakTo",1])){t[1]=["leaf","dec",6];return true;} if(Array.isArray(t)&&t.length===2)return replaceFinal(t[0])||replaceFinal(t[1]);return false;}
  assert(replaceFinal(ax),"last emitter changed");
  const hybrid=source(),hCheck=validate(hRows,hybrid.contracts);
  assert(hybrid.sites.length===3650,"hybrid sites");
  assert(eq(hCheck,{ok:true,contracts:4751,max_steps:497,total_steps:1472644}),"HAZ verification receipt");
  const startHead=-2,physical=[0,0,0,0,0,0,2,0,0,...Array(26).fill(1)];
  const path=hybrid.sites[25][0],expected=new Set([startHead-1,startHead+48]);
  path.forEach((b,i)=>{if(b)expected.add(startHead+i)});
  let pos=startHead+49;
  for(const v of physical){pos++;for(let j=0;j<=v;j++)expected.add(pos+j);pos+=v+1;}
  let state=74,head=0,ones=new Set(),startupSteps=null;
  for(let i=1;i<=100000;i++){
    const [w,d,n]=hRows[state][ones.has(head)?1:0];
    if(w)ones.add(head);else ones.delete(head);
    head+=d?1:-1;state=n;assert(state!==254,"startup halt");
    if(state===84&&head===startHead&&ones.size===expected.size&&[...ones].every(x=>expected.has(x))){startupSteps=i;break;}
  }
  assert(startupSteps===58122,"exact startup");
  const labels=[74],index=new Map([[74,0]]);
  for(let i=0;i<labels.length;i++)for(let b=0;b<2;b++){
    const n=hRows[labels[i]][b][2];
    if(n!==254&&!index.has(n)){index.set(n,labels.length);labels.push(n);}
  }
  assert(labels.length===194&&Object.keys(hRows).length===194,"reachable controls");
  labels.push(254);
  function textTable(rows,dense=false){
    return Object.keys(rows).map(Number).sort((a,b)=>a-b).flatMap(q=>rows[q].map(([w,d,n],b)=>
      [dense?index.get(q):q,b,w,d?"R":"L",dense?(n===254?194:index.get(n)):n]))
      .sort((a,b)=>a[0]-b[0]||a[1]-b[1]).map(x=>x.join(" ")).join("\n")+"\n";
  }
  return {
    baseline:baseCheck,hybrid:hCheck,sourceSites:hybrid.sites.length,
    startup:{steps:startupSteps,state,head,one_cells:[...ones].sort((a,b)=>a-b),physical_file:physical,complete_tape_equality:true},
    native:textTable(hRows),dense:textTable(hRows,true),labels,
    instructions:hybrid.ins,sites:hybrid.sites.map(([p,op,a])=>[p.join(""),op,a])
  };
}
if(typeof module!=="undefined"){
  module.exports={verifyHAZ};
  if(require.main===module){
    const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto");
    const root=path.resolve(__dirname,"..");
    const result=verifyHAZ(
      fs.readFileSync(path.join(root,"inputs/pa194.native.tm"),"utf8"),
      JSON.parse(fs.readFileSync(path.join(root,"inputs/pa194.grammar.json"),"utf8")),
      fs.readFileSync(path.join(root,"vendor/reference/PA196/Program.lean"),"utf8"));
    const sha=s=>crypto.createHash("sha256").update(s).digest("hex");
    if(sha(result.native)!=="5ffbc263413612caa71b85895a92860797d90f5c77315119134b6e30fd566f09")throw Error("Native digest");
    if(sha(result.dense)!=="f9f98218e2f949b28f0429f2bbab17babe0f4948c2e38cb786a5e3b239101981")throw Error("Dense digest");
    // Compare rather than rewrite the Python-produced artifacts.
    const sameJSON=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
    for(const [name,value] of Object.entries({"pa194haz.native.tm":result.native,"pa194haz.tm":result.dense}))
      if(fs.readFileSync(path.join(root,"machine",name),"utf8")!==value)throw Error("Python/JavaScript table disagreement: "+name);
    for(const [name,value] of Object.entries({"pa194haz.labels.json":result.labels,"pa194haz.instructions.json":result.instructions,"pa194haz.sites.json":result.sites}))
      if(!sameJSON(JSON.parse(fs.readFileSync(path.join(root,"machine",name),"utf8")),value))throw Error("Python/JavaScript source disagreement: "+name);
    const {native,dense,labels,instructions,sites,...receipt}=result;
    receipt.native_sha256=sha(native);receipt.dense_sha256=sha(dense);
    receipt.python_artifacts_agree=true;
    fs.writeFileSync(path.join(root,"verification/javascript_results.json"),JSON.stringify(receipt,null,2)+"\n");
    console.log(JSON.stringify(receipt,null,2));
  }
}
