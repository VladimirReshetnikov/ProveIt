#include <array>
#include <vector>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <algorithm>
#include <chrono>
using namespace std;
struct A{int w,d,q;};
A tab[256][2]; bool present[256];
const int S=2000001,O=S/2;int cells[S];
int main(int argc,char**argv){
 if(argc<2)return 2;ifstream f(argv[1]);string line;while(getline(f,line)){if(line.empty()||line[0]=='#')continue;istringstream ss(line);int q,b,w,t;char d;ss>>q>>b>>w>>d>>t;tab[q][b]={w,d=='R'?1:-1,t};present[q]=true;}
 tab[60][0].q=20;present[0]=present[1]=present[3]=false;
 long fuel=argc>2?stol(argv[2]):1000000;int id=0;auto began=chrono::steady_clock::now();
 for(int targ=0;targ<256;targ++){if(!present[targ])continue;
 for(int w=0;w<2;w++)for(int d:{1,-1}){
  ++id;tab[97][0]={w,d,targ};int q=targ,h=O+d,ones=w;if(w)cells[O]=id;long n;bool success=false;int visits=0;
  for(n=1;n<fuel;n++){
   if(q==254)break;
   if(q==96){
    visits++;int m=h-1;if(m>=0&&cells[m]==id){
     int j=h;while(j<S&&cells[j]!=id&&j-h<=100000)j++;
     if(j-h>=40&&j<S&&cells[j]==id){
      int header=j,cnt=2;vector<int>v;int p=header+1;
      while(p+1<S&&cells[p]!=id&&cells[p+1]==id){
       int e=p+1;while(e<S&&cells[e]==id)e++;
       int value=e-p-2;v.push_back(value);cnt+=value+1;p=e;
       if(v.size()>50000)break;
      }
      if(v.size()>=10&&cnt==ones&&v[0]==0&&v[2]==0&&v[7]==0){
       cout<<"{\"init\":["<<w<<","<<d<<","<<targ<<"],\"steps\":"<<n<<",\"head\":"<<h-O<<",\"header\":"<<header-O<<",\"ones\":"<<ones<<",\"values\":[";for(size_t z=0;z<v.size();z++){if(z)cout<<",";cout<<v[z];}cout<<"]}"<<endl;
       success=true;break;
      }
     }
    }
   }
   if(h<1||h>=S-1)break;
   int b=cells[h]==id;A a=tab[q][b];if(a.w&&!b){cells[h]=id;ones++;}else if(!a.w&&b){cells[h]=0;ones--;}q=a.q;h+=a.d;
  }
  if(id%100==0)cerr<<"checked "<<id<<" elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<"\n";
 }
 }
 cerr<<"done "<<id<<" elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-began).count()<<"\n";
}
