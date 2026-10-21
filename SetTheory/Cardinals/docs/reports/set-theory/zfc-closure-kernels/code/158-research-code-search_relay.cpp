// Two-row finite-frame repair of an already-invalid bootstrap candidate.
// Every bounded rejection is a search exclusion, not a divergence theorem.
#define SKIP_TWO_MAIN
#include "search_two.cpp"
int main(int argc,char**argv){
 if(argc!=7){cerr<<"table cases source primary_key outprefix allstarts\n";return 2;}
 vector<int>states;Table base=load_table(argv[1],states);auto cases=load_cases(argv[2]);read_source(argv[3]);int firstkey=stoi(argv[4]);string outprefix=argv[5];bool allstarts=stoi(argv[6]);
 vector<vector<int>>uses(MAXQ*2);vector<int>originalfail;
 for(int i=0;i<(int)cases.size();i++){auto r=probe(base,cases[i],true);if(r.status)originalfail.push_back(i);for(int key:r.seen)uses[key].push_back(i);}
 cerr<<"Baseline failing cases "<<originalfail.size()<<" of "<<cases.size()<<'\n';
 for(int i:originalfail)cerr<<"Failure "<<i<<" ordinal "<<cases[i].ordinal<<" positive "<<cases[i].positive<<" trial "<<cases[i].trial<<'\n';
 vector<Action>actions;for(int w:{0,1})for(int d:{-1,1}){for(int z:states)actions.push_back({w,d,z});actions.push_back({w,d,254});}
 long pairs=0,localpass=0,finitepass=0,boots=0,simsteps=0,firstactions=0;auto began=chrono::steady_clock::now();
 ofstream passfile(outprefix+"-finite.txt"),summary(outprefix+"-summary.txt");
 vector<int>firstchecks=originalfail;firstchecks.insert(firstchecks.end(),uses[firstkey].begin(),uses[firstkey].end());
 for(Action first:actions)if(!(first==base[firstkey])){
  firstactions++;Table t=base;t[firstkey]=first;int failed=-1;vector<int>secondkeys;
  for(int i:firstchecks){auto r=probe(t,cases[i],true);simsteps+=r.steps;if(r.status){failed=i;secondkeys=r.seen;break;}}
  if(failed<0){auto r=bootstrap(t,0,1000000,true);secondkeys=r.used;}
  for(int secondkey:secondkeys)if(secondkey!=firstkey){
   vector<int>checkset=firstchecks;checkset.insert(checkset.end(),uses[secondkey].begin(),uses[secondkey].end());sort(checkset.begin(),checkset.end());checkset.erase(unique(checkset.begin(),checkset.end()),checkset.end());
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
  if(firstactions%50==0)cerr<<"Primary actions "<<firstactions<<" pairs "<<pairs<<" local pass "<<localpass<<" finite pass "<<finitepass<<" boot frames "<<boots<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 }
 summary<<"primary "<<firstkey/2<<'/'<<firstkey%2<<" first actions "<<firstactions<<" pairs "<<pairs<<" local pass "<<localpass<<" finite pass "<<finitepass<<" boot frames "<<boots<<" simulation steps "<<simsteps<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<'\n';
 return 0;
}
