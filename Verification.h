#ifndef _verification_h
#define _verification_h
#include "CFG.h"
#include "general.h"
#include "MinisatDebug.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "dreal.h"
//#include "Solver.h"
#include "minisat/core/Solver.h"
//#include "dreal_c.h"
#include <fstream>
#include "LinearVerify.h"
#include "UnlinearVerify.h"

class BoundedVerification{
public:
    BoundedVerification(CFG* aut,int bound,vector<int> target,double pre, DebugInfo *dbg, int outMode);
    bool check(double &time,string check);
    double getTime(){return verify->getTime();}
    ~BoundedVerification();
private:
    Verify *verify;
    DebugInfo *dbg;
    CFG* cfg;
    double precision;
    bool result;
    bool reachEnd;
    int bound;
    int outMode;
    string reachPath;
    string target_name;
    int num_of_path;
    vector<int> target;
    vector<int> path;
    vector<int> witPath;
    string get_path_name(CFG *cfg,vector<int> path);
    void DFS(int intbound,int bound,int start,int end);
    Minisat::Solver s;
    bool solve(int cur_target);
    void encode_graph();
//    Minisat::vec<Minisat::Lit> setTarget(int cur_target);
    Minisat::Lit var(const int loop, const int ID);
    void decode(int code, int& loop, int& ID);
    void block_path(int number,CFG *cfg,vector<int> path);
    vector<int> decode_path(int cur_target);
};




#endif

