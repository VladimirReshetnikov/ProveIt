#include <bits/stdc++.h>
using namespace std;
struct T{int w,d,q;};
int main(int argc,char**argv){
 if(argc<2)return 2;ifstream in(argv[1]);static T tab[200000][2];static bool exists[200000]={};int q,b,w,t;char d;while(in>>q>>b>>w>>d>>t){tab[q][b]={w,d=='R'?1:-1,t};exists[q]=1;}
 long long cap=argc>2?stoll(argv[2]):10000000,head=0; q=74;set<long long> tape;
 map<pair<int,vector<long long>>,pair<long long,long long>> seen;
 long long roots=0;
 for(long long i=0;i<cap;i++){
  if(!exists[q]){cout<<"HALT "<<i<<" "<<q<<" "<<head<<"\n";return 0;}
  if(q==84 || i%256==0){
   vector<long long> sig;sig.push_back(head);sig.insert(sig.end(),tape.begin(),tape.end());
   auto key=make_pair(q,sig);auto z=seen.find(key);
   if(z!=seen.end()){cout<<"EXACT_CYCLE "<<z->second.first<<" "<<i<<" "<<q<<" "<<head<<" ones "<<tape.size()<<"\n";return 0;}
   seen.emplace(move(key),make_pair(i,head));
  }
  if(q==84){roots++;if(roots<=10)cout<<"ROOT "<<i<<" "<<head<<" ones "<<tape.size()<<"\n";}
  auto a=tab[q][tape.count(head)?1:0];if(a.w)tape.insert(head);else tape.erase(head);head+=a.d;q=a.q;
 }
 cout<<"CAP "<<cap<<" state "<<q<<" head "<<head<<" roots "<<roots<<" ones "<<tape.size()<<"\n";
}
