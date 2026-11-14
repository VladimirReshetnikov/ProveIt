#include <bits/stdc++.h>
#include "finite_support.cpp"
struct Tr{int w,d,z;};struct C{array<unsigned char,W> in,out;int h;bool halt;int idx;};
Tr transition_table[1000][2];vector<int>states;vector<C>cases;vector<int>cov[1000][2];
bool run(const C&c,int drop,int keep,int change,Tr candidate,bool baseline=false,int ci=-1){auto tape=c.in;int entry=drop==84?keep:84;int q=entry,h=OFF;set<pair<int,int>> used;
 for(int k=0;k<5000;k++){
  if(k&&((c.halt&&q==254)||(!c.halt&&q==entry&&h==c.h&&tape==c.out))){if(baseline)for(auto [q,b]:used)cov[q][b].push_back(ci);return true;}
  if(q==254||q<0||q>=1000||h<1||h>=W-1)return false;int b=tape[h];if(baseline)used.insert({q,b});Tr tr=transition_table[q][b];if(q==keep&&b==change)tr=candidate;if(tr.z==drop)tr.z=keep;tape[h]=tr.w;h+=tr.d;q=tr.z;
 }return false;
}
int main(int argc,char**argv){ifstream f(argv[1]);string line;set<int>ss;while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream st(line);int q,b,w,z;char d;st>>q>>b>>w>>d>>z;transition_table[q][b]={w,d=='R'?1:-1,z};ss.insert(q);}states={ss.begin(),ss.end()};vector<int>helpers=states;helpers.push_back(254);
 ifstream sf(argv[2]);vector<Site>sites;Site s;while(sf>>s.p>>s.op>>s.a)sites.push_back(s);
 for(int idx=0;idx<(int)sites.size();idx++){auto&s=sites[idx];for(int sample=0;sample<3;sample++)for(int positive=0;positive<(s.op=="CD"?2:1);positive++){
 vector<int>regs(9),spares(sample+1);for(int i=0;i<9;i++)regs[i]=sample?(i*3+sample)%4:0;for(int i=0;i<(int)spares.size();i++)spares[i]=sample?(i+sample)%3:0;if(s.op=="CD")regs[s.a]=positive?sample+1:0;int gap=sample?sample:0,shift=0,delta=0;C c;c.halt=s.op=="CH";c.idx=idx;frame(c.in,s.p,regs,spares,gap);string pc=s.p;
 if(s.op=="CI"){regs[s.a]++;spares.push_back(1);auto x=inc(pc);pc=x.first;shift=x.second;}else if(s.op=="CD"&&positive){regs[s.a]--;delta=1;auto x=inc(pc);pc=x.first;shift=x.second;}else if(s.op=="CD"||s.op=="CB"){auto x=inc(strip(pc,'0',s.op=="CD"?1:s.a));pc=x.first;shift=x.second;}else if(s.op=="CC")pc=strip(pc,'1',s.a);frame(c.out,pc,regs,spares,gap+delta+shift,shift);c.h=OFF-shift;int ci=cases.size();cases.push_back(c);if(!run(c,-1,-1,-1,{},true,ci)){cerr<<"BADBASE "<<idx<<"\n";return 2;}
 }}
 mt19937 rng(20729);vector<int>selected[1000];for(int q:states){set<int>sel;for(int b=0;b<2;b++){auto a=cov[q][b];if(!a.empty())sel.insert(a[0]);shuffle(a.begin(),a.end(),rng);for(int i=0;i<min((int)a.size(),8);i++)sel.insert(a[i]);}selected[q]={sel.begin(),sel.end()};}
 long trials=0,pre=0,pairs=0;int successes=0;
 for(int drop:states)for(int keep:states){if(drop==keep)continue;set<int>sels(selected[drop].begin(),selected[drop].end());sels.insert(selected[keep].begin(),selected[keep].end());vector<int>pick(sels.begin(),sels.end());
 for(int change=0;change<2;change++){auto a=transition_table[drop][1-change],b=transition_table[keep][1-change];if(a.z==drop)a.z=keep;if(b.z==drop)b.z=keep;if(a.w!=b.w||a.d!=b.d||a.z!=b.z)continue;pairs++;
 for(int z:helpers){if(z==drop)continue;for(int w=0;w<2;w++)for(int d:{-1,1}){trials++;Tr cand={w,d,z};bool ok=true;for(int i:pick){if(!run(cases[i],drop,keep,change,cand)){ok=false;break;}}if(!ok)continue;pre++;for(auto &c:cases)if(!run(c,drop,keep,change,cand)){ok=false;break;}if(ok){cout<<drop<<" "<<keep<<" "<<change<<" "<<w<<" "<<d<<" "<<z<<"\n";cout.flush();successes++;}
 }} }}cerr<<"cases "<<cases.size()<<" pairs "<<pairs<<" trials "<<trials<<" targeted "<<pre<<" successes "<<successes<<"\n";
}
