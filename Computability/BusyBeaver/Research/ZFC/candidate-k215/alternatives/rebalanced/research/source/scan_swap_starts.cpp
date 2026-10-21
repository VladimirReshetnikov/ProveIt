#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

struct Step{int w=0,d=0,z=-1;};
struct Result{int start,q;int64_t steps,h;std::string status;std::vector<int64_t> regs,spares,ones;};
std::array<std::array<Step,2>,512> T;
std::set<int> states;
bool seed(int64_t h,const std::set<int64_t>&ones,Result&r){
    if(ones.empty()||*ones.begin()!=h-1)return false;
    auto it=ones.begin();++it;if(it==ones.end()||*it<h+64)return false;
    int64_t header=*it,p=header+1,last=*ones.rbegin();std::vector<int64_t>v;
    while(p<=last){
        if(ones.count(p)||!ones.count(p+1))return false;
        ++p;int64_t n=0;while(ones.count(p)){++n;++p;}v.push_back(n-1);
    }
    if(v.size()<10||v[0]!=0||v[2]!=0||v[7]!=0)return false;
    int phy[9]={6,2,0,4,3,7,8,5,1};for(int j=0;j<9;j++)r.regs.push_back(v[phy[j]]);
    r.spares.assign(v.begin()+9,v.end());r.ones.assign(ones.begin(),ones.end());return true;
}
Result run(int start,int64_t limit){
    int q=start;int64_t h=0;std::set<int64_t>ones;
    for(int64_t tick=0;tick<=limit;tick++){
        Result r{start,q,tick,h,""};
        if(q==84&&seed(h,ones,r)){r.status="SAFE_ROOT_SEED";return r;}
        if(q==254){r.status="HALT";return r;}
        int b=ones.count(h);Step a=T[q][b];
        if(a.z<0){r.status="UNDEFINED";return r;}
        if(b==0&&a.z==q&&(ones.empty()||(a.d>0&&h>*ones.rbegin())||(a.d<0&&h<*ones.begin()))){r.status="EXACT_OUTWARD_RAY";return r;}
        if(tick==limit){r.status="BOUND_EXHAUSTED";return r;}
        if(a.w)ones.insert(h);else ones.erase(h);h+=a.d;q=a.z;
    }
    return {};
}
template<class X>void list(const X&v){std::cout<<"[";bool first=true;for(auto x:v){if(!first)std::cout<<",";first=false;std::cout<<x;}std::cout<<"]";}
int main(int argc,char**argv){
    if(argc!=3)return 2;std::ifstream in(argv[1]);std::string line;
    while(std::getline(in,line)){if(line.empty()||line[0]=='#')continue;std::istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};states.insert(q);}
    int64_t limit=std::stoll(argv[2]);std::cout<<"{\"step_limit_per_start\":"<<limit<<",\"results\":[\n";bool first=true;
    for(int start:states){auto r=run(start,limit);if(!first)std::cout<<",\n";first=false;
        std::cout<<"{\"start\":"<<r.start<<",\"status\":\""<<r.status<<"\",\"steps\":"<<r.steps<<",\"state\":"<<r.q<<",\"head\":"<<r.h;
        if(r.status=="SAFE_ROOT_SEED"){
            std::set<int>reach={start};std::vector<int>todo={start};for(size_t j=0;j<todo.size();j++)for(int b=0;b<2;b++){int z=T[todo[j]][b].z;if(z!=254&&reach.insert(z).second)todo.push_back(z);}
            std::cout<<",\"reachable_working_states\":"<<reach.size()<<",\"registers\":";list(r.regs);std::cout<<",\"spares\":";list(r.spares);std::cout<<",\"ones\":";list(r.ones);
        }
        std::cout<<"}"<<std::flush;
    }
    std::cout<<"\n]}\n";
}
