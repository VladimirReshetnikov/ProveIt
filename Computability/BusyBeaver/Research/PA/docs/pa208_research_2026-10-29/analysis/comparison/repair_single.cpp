#define main finite_old_main
#include "finite_fast.cpp"
#undef main
bool try_case(const Site& site, bool positive, set<pair<int,int>>* visited=nullptr) {
 vector<int> regs(9,0),spares(1,0);if(site.operation=="CD"&&positive)regs[site.argument]=1;
 auto tape=frame(site.address,regs,spares,0);string pc=site.address;int shift=0,delta=0;
 if(site.operation=="CI"){++regs[site.argument];spares.push_back(1);tie(pc,shift)=increment(pc);}
 else if(site.operation=="CD"&&positive){--regs[site.argument];delta=1;tie(pc,shift)=increment(pc);}
 else if(site.operation=="CD"||site.operation=="CB")tie(pc,shift)=increment(strip(pc,'0',site.operation=="CD"?1:site.argument));
 else if(site.operation=="CC")pc=strip(pc,'1',site.argument);
 auto uns=frame(pc,regs,spares,delta+shift);set<int> expected;for(int p:uns)expected.insert(p-shift);
 int q=84,h=0;
 for(int tick=0;tick<2500;++tick){
  if(tick>0&&q==254)return site.operation=="CH";
  if(tick>0&&q==84&&h==-shift&&tape==expected)return true;
  int bit=tape.count(h);if(visited)visited->insert({q,bit});step(q,h,tape);
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=3)return 2;ifstream f(argv[1]);string line;vector<int>states;
 while(getline(f,line)){if(line.empty()||line[0]=='#')continue;int q,b,w,z;char d;istringstream s(line);s>>q>>b>>w>>d>>z;machine[q][b]={w,d=='R'?1:-1,z};if(b==0)states.push_back(q);}
 ifstream source(argv[2]);vector<Site>sites;string p,o;int a;while(source>>p>>o>>a)sites.push_back({p,o,a});
 vector<pair<int,bool>>cases;
 for(int i=0;i<int(sites.size());++i){cases.push_back({i,false});if(sites[i].operation=="CD")cases.push_back({i,true});}
 int first=-1;set<pair<int,int>>visited;
 for(int c=0;c<int(cases.size());++c){auto [i,pos]=cases[c];if(!try_case(sites[i],pos)){first=c;try_case(sites[i],pos,&visited);break;}}
 cerr<<"first "<<first<<" site "<<cases[first].first<<" visited "<<visited.size()<<"\n";
 int n=0,pass=0,best=0;vector<pair<int,bool>> reordered;reordered.push_back(cases[first]);for(int c=0;c<int(cases.size());++c)if(c!=first)reordered.push_back(cases[c]);
 for(auto[q,b]:visited){Transition old=machine[q][b];
  for(int z:states)for(int w=0;w<2;++w)for(int d:{-1,1}){if(w==old.write&&d==old.move&&z==old.target)continue;++n;machine[q][b]={w,d,z};int success=0;
   for(auto[i,pos]:reordered){if(!try_case(sites[i],pos))break;++success;}
   if(success>best){best=success;cerr<<"BEST "<<best<<" "<<q<<" "<<b<<" "<<w<<" "<<d<<" "<<z<<"\n";}
   if(success==int(reordered.size())){++pass;cout<<q<<" "<<b<<" "<<w<<" "<<(d==1?"R":"L")<<" "<<z<<"\n";cout.flush();}
  }
  machine[q][b]=old;
 }
 cerr<<"scans "<<n<<" passed "<<pass<<" best "<<best<<"\n";
}
