#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,n;bool operator==(const Act&o)const{return w==o.w&&d==o.d&&n==o.n;} bool operator!=(const Act&o)const{return !(*this==o);}};
struct Key{Act a,b;bool operator==(const Key&o)const{return a==o.a&&b==o.b;}};
struct KH{size_t operator()(const Key&k)const{return ((k.a.w*2+k.a.d)*400+k.a.n)*1700000ull+((k.b.w*2+k.b.d)*400+k.b.n);}};
struct Opt{int a,b;array<vector<Act>,2> acts;};
int main(int argc,char**argv){
 ifstream f(argv[1]); int q,b,w,t;char d;map<int,array<Act,2>> src;while(f>>q>>b>>w>>d>>t)src[q][b]={w,d=='R',t};
 vector<int> labels;map<int,int> idx;for(auto [q,r]:src){idx[q]=labels.size();labels.push_back(q);}int n=labels.size();idx[254]=n;
 vector<array<Act,2>> base(n);for(int i=0;i<n;i++)for(int b=0;b<2;b++){auto a=src[labels[i]][b];a.n=idx.at(a.n);base[i][b]=a;}
 set<int> boxes={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198};
 int skips[9]={51,36,25,48,32,33,22,55,60};map<int,int> isk;for(int i=0;i<9;i++)isk[idx.at(skips[i])]=i;
 vector<tuple<int,int,int>> edits;for(int i=0;i<n;i++)for(int b=0;b<2;b++){auto a=base[i][b];if(!boxes.count(labels[i])&&a.w==0&&a.d==1&&isk.count(a.n))edits.push_back({i,b,isk.at(a.n)});}
 cerr<<"states "<<n<<" edits "<<edits.size()<<"\n";
 vector<int> perm={0,1,2,3,4,5,6,7,8};map<int,int> hist;long long total=0,eligible=0,hits=0;int best=-1;
 do{
  total++; if(argc>2&&perm[6]!=6)continue;eligible++;
  auto rows=base;for(auto [q,b,r]:edits)rows[q][b].n=idx.at(skips[perm[r]]);
  vector<int> incoming(n);incoming[idx.at(74)]=4;
  for(int i=0;i<n;i++)for(int b=0;b<2;b++){auto a=rows[i][b];if(a.n<n)incoming[a.n]|=(a.w==b&&a.d==1)?(1<<b):4;}
  vector<int> left,right;for(int i=0;i<n;i++){if(boxes.count(labels[i]))continue;if(incoming[i]==1)left.push_back(i);if(incoming[i]==2)right.push_back(i);}
  array<unordered_map<Key,vector<int>,KH>,2> providers;
  for(int h=0;h<n;h++)if(rows[h][0].w==0&&rows[h][0].d&&rows[h][1].w==1&&rows[h][1].d){int u=rows[h][0].n,v=rows[h][1].n;if(u<n&&v<n)for(int b=0;b<2;b++)providers[b][Key{rows[u][b],rows[v][b]}].push_back(h);}
  vector<Opt> ops;vector<vector<int>> edges(n);
  for(int a:left)for(int c:right){Opt op{a,c,{}};bool good=true;for(int b=0;b<2;b++){
    if(rows[a][b]==rows[c][b])op.acts[b].push_back(rows[a][b]);
    else{auto it=providers[b].find(Key{rows[a][b],rows[c][b]});if(it!=providers[b].end())for(int h:it->second){int u=rows[h][0].n,v=rows[h][1].n;if(h!=a&&h!=c&&u!=a&&u!=c&&v!=a&&v!=c)op.acts[b].push_back({b,0,h});}}
    if(op.acts[b].empty())good=false;
  }if(good){ops.push_back(op);edges[a].push_back(c);}}
  vector<int> match(n,-1);int score=0;function<bool(int,vector<int>&)> aug=[&](int a,vector<int>&seen){for(int b:edges[a])if(!seen[b]){seen[b]=1;if(match[b]<0||aug(match[b],seen)){match[b]=a;return true;}}return false;};for(int a:left){vector<int>seen(n);if(aug(a,seen))score++;}
  hist[score]++;if(score>best){best=score;cerr<<"best "<<best<<" perm ";for(int x:perm)cerr<<x;cerr<<" total "<<eligible<<"\n";}
  if(score>=8){hits++;cout<<"{\"perm\":[";for(int i=0;i<9;i++)cout<<(i?",":"")<<perm[i];cout<<"],\"score\":"<<score<<",\"ops\":[";bool first=true;for(auto op:ops){if(!first)cout<<",";first=false;cout<<"["<<labels[op.a]<<","<<labels[op.b]<<",[";for(int b=0;b<2;b++){if(b)cout<<",";cout<<"[";bool ff=true;for(auto a:op.acts[b]){if(!ff)cout<<",";ff=false;cout<<"["<<a.w<<","<<a.d<<","<<(a.n==n?254:labels[a.n])<<"]";}cout<<"]";}cout<<"]]";}cout<<"]}\n";}
 }while(next_permutation(perm.begin(),perm.end()));
 cerr<<"DONE total="<<total<<" eligible="<<eligible<<" hits="<<hits<<" hist=";for(auto [k,v]:hist)cerr<<k<<":"<<v<<",";cerr<<"\n";
}
