#define SKIP_REPLAY_MAIN
#include "replay_survivors.cpp"
struct Probe{int status;long steps;vector<int>seen;};
Probe probe(const Table&t,const Case&c,bool record=false,int cap=5000){
 Tape tape=c.input;int q=84,h=0;bitset<MAXQ*2>seen;
 Tape checkpoint=tape;int cq=q,ch=h,power=1,distance=0;
 auto finish=[&](int status,int k){vector<int>v;if(record)for(int i=0;i<MAXQ*2;i++)if(seen[i])v.push_back(i);return Probe{status,k,v};};
 for(int k=0;k<=cap;k++){
  if(q==254)return finish(c.targetq==254?0:1,k);
  if(k&&q==84){if(c.targetq==84&&h==c.targeth&&tape==c.target)return finish(0,k);if(clean(h,tape))return finish(1,k);}
  if(k&&q==cq&&h==ch&&tape==checkpoint)return finish(6,k);
  if(distance==power){checkpoint=tape;cq=q;ch=h;power*=2;distance=0;}
  if(k==cap)return finish(2,k);
  if(h<-OFFSET+2||h>=WIDTH-OFFSET-2)return finish(3,k);
  int b=tape.read(h),key=2*q+b;Action a=t[key];if(a.w<0)return finish(4,k);if(record)seen[key]=true;
  if(!b&&a.z==q&&((a.d==1&&h>=tape.hi)||(a.d==-1&&h<=tape.lo)))return finish(5,k);
  tape.write(h,a.w);h+=a.d;q=a.z;distance++;
 }
 throw runtime_error("unreachable");
}
#ifndef SKIP_TWO_MAIN
int main(int argc,char**argv){
 if(argc!=7){cerr<<"table cases source primary_key outprefix allstarts\n";return 2;}
 vector<int>states;Table base=load_table(argv[1],states);auto cases=load_cases(argv[2]);read_source(argv[3]);int firstkey=stoi(argv[4]);string outprefix=argv[5];bool allstarts=stoi(argv[6]);
 vector<vector<int>>uses(MAXQ*2);
 for(int i=0;i<(int)cases.size();i++){auto r=probe(base,cases[i],true);if(r.status)throw runtime_error("baseline failure");for(int key:r.seen)uses[key].push_back(i);}
 vector<Action>actions;for(int w:{0,1})for(int d:{-1,1}){for(int z:states)actions.push_back({w,d,z});actions.push_back({w,d,254});}
 long pairs=0,localpass=0,finitepass=0,boots=0,simsteps=0,firstactions=0;auto began=chrono::steady_clock::now();
 ofstream passfile(outprefix+"-finite.txt"),summary(outprefix+"-summary.txt");
 for(Action first:actions)if(!(first==base[firstkey])){
  firstactions++;Table t=base;t[firstkey]=first;int failed=-1;vector<int>secondkeys;
  for(int i:uses[firstkey]){auto r=probe(t,cases[i],true);simsteps+=r.steps;if(r.status){failed=i;secondkeys=r.seen;break;}}
  if(failed<0){
   auto r=bootstrap(t,0,1000000,true);secondkeys=r.used;
  }
  for(int secondkey:secondkeys)if(secondkey!=firstkey){
   vector<int>checkset=uses[firstkey];checkset.insert(checkset.end(),uses[secondkey].begin(),uses[secondkey].end());sort(checkset.begin(),checkset.end());checkset.erase(unique(checkset.begin(),checkset.end()),checkset.end());
   for(Action second:actions)if(!(second==base[secondkey])){
    pairs++;t[secondkey]=second;
    if(failed>=0){auto r=probe(t,cases[failed]);simsteps+=r.steps;if(r.status){t[secondkey]=base[secondkey];continue;}}
    localpass++;bool good=true;
    for(int i:checkset){if(i==failed)continue;auto r=probe(t,cases[i]);simsteps+=r.steps;if(r.status){good=false;break;}}
    if(good){
     finitepass++;passfile<<firstkey/2<<' '<<firstkey%2<<' '<<first.w<<' '<<first.d<<' '<<first.z<<' '<<secondkey/2<<' '<<secondkey%2<<' '<<second.w<<' '<<second.d<<' '<<second.z<<'\n'<<flush;
     vector<int>starts={0};if(allstarts)starts=states;
     for(int start:starts){auto r=bootstrap_any(t,start,1000000);simsteps+=r.steps;if(r.status==0){
      boots++;auto f=any_frame(r.h,r.tape);cout<<"{\"rows\":[["<<firstkey/2<<','<<firstkey%2<<','<<first.w<<','<<first.d<<','<<first.z<<"],["<<secondkey/2<<','<<secondkey%2<<','<<second.w<<','<<second.d<<','<<second.z<<"]],\"start\":"<<start<<",\"steps\":"<<r.steps<<",\"head\":"<<r.h<<",\"ordinal\":"<<f.ordinal<<",\"gap_registers_spares\":";dump_array(f.values);cout<<",\"support\":";dump_support(r.tape);cout<<"}\n"<<flush;
     }}
    }
    t[secondkey]=base[secondkey];
   }
  }
  if(firstactions%50==0)cerr<<"FIRST "<<firstactions<<" pairs "<<pairs<<" localpass "<<localpass<<" finitepass "<<finitepass<<" boots "<<boots<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 }
 summary<<"primary "<<firstkey/2<<'/'<<firstkey%2<<" firstactions "<<firstactions<<" pairs "<<pairs<<" localpass "<<localpass<<" finitepass "<<finitepass<<" boots "<<boots<<" simulation_steps "<<simsteps<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 return 0;
}
#endif
