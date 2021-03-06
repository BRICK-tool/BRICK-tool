#ifndef _linearverify_h
#define _linearverify_h
#include "CFG.h"
#include "general.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "z3++.h"
#include "MUSSAnalyzer.h"
#include "math.h"
#include "DebugInfo.h"


class LinearVarTable{
private:
    int var_num;
    int alloca_num;
    map<int, double> varVal;
    map<int, int>storeMap;
    map<int, int> alias;
    vector<z3::expr> x;
    map<int, int> exprMap;
    CFG *cfg;
public:
    LinearVarTable(z3::context &ctx, CFG *ha);
    ~LinearVarTable();
    void setX(int ID, int time, VarType type, z3::context &ctx);
    int alloca();
    void setAlias(int ID1, int ID2);
    void setAlias(Variable *v1, Variable *v2);
    void setVal(int ID, double val);
    void store(int ID1, int ID2);
    int getNum();
    z3::expr getX(int ID);
    int load(int ID);
    bool hasAlias(Variable *v);
    Variable* getAlias(int ID);
    Variable* getAlias(Variable* var);
    bool getVal(Variable *var, double &v);
    bool getVal(int ID, double &v);
    map<int, double> getValmap();
    map<int, int> getAliasmap();
    CFG *getCFG();
};

class LinearVerify: public Verify{
    z3::context c;
    int outMode;
    DebugInfo *dbg;
    double time;

    z3::expr_vector encode_path(CFG* ha, vector<int> path);
    z3::expr getExpr(Variable *v, bool &treat, double &val, LinearVarTable *table);
    z3::expr mk_INT_cmp(z3::expr y, z3::expr z, Op_m pvop);
    int getCMP(int rl, int rr, Op_m pvop);
    void get_constraint(Constraint *con, LinearVarTable *table, int time, z3::expr_vector &p);
    bool analyze_unsat_core(SubsetSolver& csolver, MapSolver& msolver);
    void add_IIS(IndexPair index);
    std::vector<IndexPair> index_cache; 
    std::vector<IndexPair> core_index;     
    void clear(){index_cache.clear();core_index.clear();}
public:
    LinearVerify(){time=0;}
    LinearVerify(DebugInfo *d, int mode){
        time=0;
        this->dbg = d;
        this->outMode = mode;
    }
    ~LinearVerify(){clear();}
    bool check(CFG* ha, vector<int> path);
    vector<IndexPair> get_core_index(){return core_index;}
    double getTime(){return time;}
    void print_sol(CFG* cfg);
};

#endif

