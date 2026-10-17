// Independent C++ port of the source27 finite affine diagnostic rules.
// The four register-box summaries are explicit conditional contracts.
// Every positive recipe must be checked afresh by the original Python rules.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

struct Action {int w=0,d=1,t=-1;};
using Table=std::array<std::array<Action,2>,512>;
struct Seg {
    int type,b,a,c;
    bool operator==(const Seg&o)const{return std::tie(type,b,a,c)==std::tie(o.type,o.b,o.a,o.c);}
};
using Side=std::deque<Seg>;
Seg bit(int b){return {0,b,0,1};}
Seg run(int b,int a,int c){return {1,b,a,c};}
Seg box(int kind=0,int reg=-1){return {2,kind,reg,0};}
Side canonical(const Side&s,bool left){
    Side out;
    for(auto x:s){
        if(x.type==2){out.push_back(x);continue;}
        if(x.type==0)x=run(x.b,0,1);
        assert(x.a>=0&&x.c>=0);
        if(x.a==0&&x.c==0)continue;
        if(!out.empty()&&out.back().type==1&&out.back().b==x.b){out.back().a+=x.a;out.back().c+=x.c;}
        else out.push_back(x);
    }
    if(left)while(!out.empty()&&out.back().type==1&&out.back().b==0)out.pop_back();
    return out;
}
struct Case {std::string pc,next;int reg,zero,halt,gap,effect,ereg,cost;Side targetL,targetR;};
struct Family {int dead;std::array<std::pair<int,int>,2> incoming;std::vector<int> affected;};
struct Result{int status,rules,literal;};
// status: 0 pass; -1/-2 pending incoming action; positives are diagnostic stops.
// 1 fuel, 2 unknown run, 3 unsupported box, 4 missing row, 5 malformed side.
Result check(const Table&t,const Case&c,const Family*family=nullptr,
             const std::array<int,2>&assigned={-1,-1},int fuel=1000){
    int q=96,literal=0;bool onleft=false;Side left{bit(1)},right;
    for(char b:c.pc)right.push_back(bit(b-'0'));
    right.push_back(run(0,1,40-int(c.pc.size())));right.push_back(bit(1));right.push_back(box());
    auto lookup=[&](int b,Action&out)->int{
        if(family)for(int i=0;i<2;++i)if(family->incoming[i]==std::pair<int,int>{q,b}&&assigned[i]<0)return -1-i;
        if(q<0||q>=512||t[q][b].t<0)return 4;
        out=t[q][b];return 0;
    };
    for(int step=0;step<fuel;++step){
        if(literal>0){
            if(c.halt&&q==254)return {0,step,literal};
            if(!c.halt&&!onleft&&q==96&&canonical(left,true)==c.targetL&&canonical(right,false)==c.targetR)return {0,step,literal};
        }
        if(onleft){
            if(left.empty()){right.push_front(bit(0));onleft=false;continue;}
            Seg x=left.front();
            if(x.type==0){left.pop_front();right.push_front(x);onleft=false;continue;}
            if(x.type!=1)return {5,step,literal};
            Action a;int failure=lookup(x.b,a);if(failure)return {failure,step,literal};
            if(a.d==-1&&a.t==q){left.pop_front();right.push_front(run(a.w,x.a,x.c));continue;}
            if(x.c>0){left.front().c--;left.push_front(bit(x.b));continue;}
            if(x.a==0){left.pop_front();continue;}
            return {2,step,literal};
        }
        if(right.empty())return {5,step,literal};
        Seg x=right.front();
        if(x.type==0){
            Action a;int failure=lookup(x.b,a);if(failure)return {failure,step,literal};
            q=a.t;++literal;
            if(a.d==1){left.push_front(bit(a.w));right.pop_front();}
            else{right.front()=bit(a.w);onleft=true;}
            continue;
        }
        if(x.type==1){
            Action a;int failure=lookup(x.b,a);if(failure)return {failure,step,literal};
            if(a.d==1&&a.t==q){left.push_front(run(a.w,x.a,x.c));right.pop_front();continue;}
            if(x.c>0){right.front().c--;right.push_front(bit(x.b));continue;}
            if(x.a==0){right.pop_front();continue;}
            return {2,step,literal};
        }
        if(x.type!=2||right.size()!=1)return {5,step,literal};
        const std::array<int,9> skip{60,44,31,56,38,40,28,64,69};
        bool applied=false;
        if(x.b==0)for(int r=0;r<9;++r)if(q==skip[r]){q=r==0?2:6;right.front()=box(1,r);onleft=true;applied=true;break;}
        if(applied)continue;
        if(x.b==1&&x.a>=0&&x.a<9){
            int r=x.a;
            if(q==73){q=48;right.front()=box(2,r);onleft=true;continue;}
            if(q==43&&c.reg==r){
                q=c.zero?3:(r==0?63:48);
                right.front()=c.zero?box():box(3,r);onleft=true;continue;
            }
        }
        Action a;int failure=lookup(0,a);if(failure)return {failure,step,literal};
        if(a.w!=0||a.d!=-1)return {3,step,literal};
        q=a.t;onleft=true;++literal;
    }
    return {1,fuel,literal};
}

std::vector<Case> readCases(const std::string&path){
    std::ifstream f(path);assert(f);std::vector<Case> out;Case c;
    while(f>>c.pc>>c.reg>>c.zero>>c.halt>>c.next>>c.gap>>c.effect>>c.ereg>>c.cost){
        if(c.next=="_")c.next="";c.targetL=canonical(Side{bit(1)},true);Side r;
        for(char b:c.next)r.push_back(bit(b-'0'));
        r.push_back(run(0,1,c.gap-int(c.next.size())));r.push_back(bit(1));r.push_back(box(c.effect,c.ereg));
        c.targetR=canonical(r,false);out.push_back(c);
    }
    assert(out.size()==8408);return out;
}
Table readTable(const std::string&path){
    std::ifstream f(path);assert(f);Table t;std::string line;int count=0;
    while(std::getline(f,line)){
        if(line.empty()||line[0]=='#')continue;
        std::istringstream s(line);int q,b,w,n;char d;s>>q>>b>>w>>d>>n;assert(s);
        t[q][b]={w,d=='R'?1:-1,n};++count;
    }
    assert(count==508);return t;
}
struct Fold {int dead;std::vector<int> cases;};
int main(int argc,char**argv){
    if(argc!=3){std::cerr<<"Usage: variant_fold_search DATA_DIRECTORY OUTPUT_PREFIX\n";return 2;}
    std::string dir=argv[1],prefix=argv[2];auto t=readTable(dir+"/baseline.tm");auto cases=readCases(dir+"/cases.tsv");
    for(size_t i=0;i<cases.size();++i){auto r=check(t,cases[i]);if(r.status||r.literal<=0){std::cerr<<"Baseline failure "<<i<<' '<<r.status<<'\n';return 3;}}
    std::vector<int> states;for(int q=0;q<512;++q)if(t[q][0].t>=0)states.push_back(q);assert(states.size()==254);
    std::ifstream input(dir+"/folds.tsv");assert(input);std::vector<Fold> folds;Fold f;int n;
    while(input>>f.dead>>n){f.cases.resize(n);for(int&i:f.cases)input>>i;assert(input);folds.push_back(f);}
    assert(folds.size()==223);
    std::ofstream ledger(prefix+".ledger.tsv"),out(prefix+".summary.json");assert(ledger&&out);
    ledger<<"deleted\treplacement\tfirst_failure\treason\tchecks\n";
    uint64_t checks=0,recipes=0,survivors=0;auto start=std::chrono::steady_clock::now();std::array<uint64_t,6> reasons{};
    std::cout<<"BASELINE 8408 PASS; recipes="<<folds.size()*(states.size()-1)<<'\n'<<std::flush;
    for(auto&f:folds){
        for(int replacement:states){
            if(replacement==f.dead)continue;Table candidate=t;
            candidate[f.dead][0].t=candidate[f.dead][1].t=-1;
            for(int q:states)if(q!=f.dead)for(int b=0;b<2;++b)if(candidate[q][b].t==f.dead)candidate[q][b].t=replacement;
            int failure=-1,reason=0;uint64_t used=0;
            for(int i:f.cases){auto r=check(candidate,cases[i]);++checks;++used;if(r.status){failure=i;reason=r.status;break;}}
            if(failure<0)for(int i=0;i<int(cases.size());++i){auto r=check(candidate,cases[i]);++checks;++used;if(r.status){failure=i;reason=r.status;break;}}
            if(failure<0){
                ++survivors;std::string name=prefix+"_"+std::to_string(f.dead)+"_"+std::to_string(replacement)+".tm";
                std::ofstream tm(name);tm<<"#! start 64\n";
                for(int q:states)if(q!=f.dead)for(int b=0;b<2;++b){auto a=candidate[q][b];tm<<q<<' '<<b<<' '<<a.w<<' '<<(a.d==1?'R':'L')<<' '<<a.t<<'\n';}
                std::cout<<"SURVIVOR "<<f.dead<<" -> "<<replacement<<'\n'<<std::flush;
            }else ++reasons[reason];
            ledger<<f.dead<<'\t'<<replacement<<'\t'<<failure<<'\t'<<reason<<'\t'<<used<<'\n';++recipes;
        }
    }
    double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    out<<"{\n  \"baseline_cases\": 8408,\n  \"baseline_states\": 254,\n  \"eligible_deletions\": 223,\n  \"recipes\": "<<recipes<<",\n  \"checks\": "<<checks<<",\n  \"survivors\": "<<survivors<<",\n  \"elapsed_seconds\": "<<elapsed<<",\n  \"failure_counts\": [";
    for(int i=0;i<6;++i){if(i)out<<',';out<<reasons[i];}out<<"]\n}\n";
    std::cout<<"FINAL recipes="<<recipes<<" checks="<<checks<<" survivors="<<survivors<<" seconds="<<elapsed<<'\n';
}
