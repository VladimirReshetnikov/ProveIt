// Exhaust every existing designated start state on the blank tape.  Accept
// only a complete clean zero-PC frame with the required nine logical values.
// This is a finite bootstrap search, not a negative theorem about all time.
#include <array>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <vector>
using namespace std;
struct Row{int w,d,z;};
int main(int argc,char**argv){
 if(argc<2)return 2;
 long long bound=argc>2?stoll(argv[2]):3000000;
 array<array<Row,2>,2048>T{};set<int>states;string line;
 ifstream in(argv[1]);while(getline(in,line)){
  if(line.empty()||line[0]=='#')continue;
  stringstream ss(line);int q,b,w,z;char d;if(!(ss>>q>>b>>w>>d>>z))return 2;
  T[q][b]={w,d=='R'?1:-1,z};states.insert(q);
 }
 const int width=65536,origin=width/2;
 const vector<int>wanted{0,0,0,3,0,0,3,0,0};
 int hits=0,attempts=0;
 int patched=argc>3?stoi(argv[3]):198,read=argc>4?stoi(argv[4]):0;
 for(int sw:{0,1})for(int sd:{-1,1})for(int sz:states){
  int start=0;attempts++;
  vector<unsigned char>t(width);set<int>ones;if(sw){t[origin]=1;ones.insert(origin);}int q=sz,h=origin+sd;string reason="BOUND";long long n=0;
  for(;n<bound;n++){
   if(!states.count(q)){reason="HALT";break;}
   if(h<2||h>=width-2){reason="TAPE_SEARCH_LIMIT";break;}
   if(q==84&&ones.size()>=11&&!ones.empty()&&*ones.begin()==h-1){
    auto it=ones.upper_bound(h-1);
    if(it!=ones.end()&&*it>=h+64){
     int header=*it,gap=header-h-64,cursor=header+1;vector<int>values;
     bool valid=true;
     while(cursor<=*ones.rbegin()){
      if(t[cursor]||!t[cursor+1]){valid=false;break;}
      int count=0;cursor++;
      while(cursor<width&&t[cursor]){count++;cursor++;}
      values.push_back(count-1);
     }
     if(valid&&values.size()>=10&&values[0]==0&&values[2]==0&&values[4]==0&&values[5]==0&&values[7]==0&&values[8]==0){
      // Any finite nonempty list of natural spare values is admissible.
      if(valid){
       hits++;reason="HIT";cout<<"HIT patch "<<patched<<" "<<read<<" "<<sw<<" "<<sd<<" "<<sz<<" start "<<start<<" steps "<<n<<" head "<<h-origin<<" gap "<<gap<<" spares "<<values.size()-9<<" one_cells";
       for(int x:ones)cout<<" "<<x-origin;cout<<" spare_values";for(size_t j=9;j<values.size();j++)cout<<" "<<values[j];cout<<"\n"<<flush;break;
      }
     }
    }
   }
   auto row=T[q][t[h]];
   // A self-loop reading zero, moving into the infinite blank exterior,
   // cannot leave that state or halt regardless of what it writes behind.
   if(!t[h]&&row.z==q&&(ones.empty()||(row.d==1?h>*ones.rbegin():h<*ones.begin()))){reason="PROVED_BLANK_RAY_LOOP";break;}
   if(row.w){t[h]=1;ones.insert(h);}else{t[h]=0;ones.erase(h);}
   h+=row.d;q=row.z;
  }
  cerr<<"PATCH "<<patched<<" "<<read<<" "<<sw<<" "<<sd<<" "<<sz<<" START "<<start<<" steps "<<n<<" state "<<q<<" head "<<h-origin<<" reason "<<reason<<" ones "<<ones.size()<<"\n";
 }
 cerr<<"FINISHED patches "<<attempts<<" bound "<<bound<<" hits "<<hits<<"\n";
}
