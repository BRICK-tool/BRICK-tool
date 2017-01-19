#ifndef _unlinearverify_h
#define _unlinearverify_h
#include "CFG.h"
#include "general.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "opensmt_c.h"
//#include "dreal.h"
//#include "Solver.h"
//#include "opensmt_c.h"
#include <fstream>
#include "math.h"
#include "DebugInfo.h"

extern int smt2set_in   (FILE *);
extern int smt2parse    ();
extern int m_argc;
extern char ** m_argv;

class UnlinearVarTable{
private:
    opensmt_context &ctx;
    int var_num;
    int alloca_num;
    map<int, double> varVal;
    map<int, int>storeMap;
    map<int, int> alias;
    vector<opensmt_expr> x;
    map<int, int> exprMap;
    CFG *cfg;
public:
    UnlinearVarTable(opensmt_context &c, CFG *ha);

    ~UnlinearVarTable();

    void setX(int ID, int time, VarType type);
    int alloca();
    void setAlias(int ID1, int ID2);
    void setAlias(Variable *v1, Variable *v2);
    void setVal(int ID, double val);
    void store(int ID1, int ID2);
    int getNum();
    opensmt_expr getX(int ID);
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

class UnlinearVerify: public Verify{

    string smt;
    opensmt_context ctx;
    UnlinearVarTable *table;
    double time;
    double precision;
    int outMode;
    DebugInfo *dbg;

    opensmt_expr getExpr(Variable *v, bool &treat, double &val, UnlinearVarTable *table);
    opensmt_expr opensmt_mk_AND(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num);
    opensmt_expr opensmt_mk_NAND(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num);
    opensmt_expr opensmt_mk_OR(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num);
    opensmt_expr opensmt_mk_XOR(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num);
    opensmt_expr opensmt_mk_SREM(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name);
    opensmt_expr opensmt_mk_ASHR(opensmt_context ctx, opensmt_expr y, int rr, string name, unsigned num);
    opensmt_expr opensmt_mk_SHL(opensmt_context ctx, opensmt_expr y, int rr, string name, unsigned num);
    opensmt_expr opensmt_mk_INT_cmp(opensmt_context ctx, opensmt_expr x, opensmt_expr y, opensmt_expr z, Op_m pvop, string name);
    int getCMP(int rl, int rr, Op_m pvop);
    opensmt_expr tran_constraint(Constraint *con, UnlinearVarTable *table, int time);
    void get_constraint(vector<Constraint> consList, UnlinearVarTable *table, int time, bool isTransition);
    void encode_path(CFG* ha, vector<int> patharray);

    std::vector<IndexPair> index_cache; 
    std::vector<IndexPair> core_index;

    bool analyze_unsat_core(int state);
    void add_IIS(IndexPair index);

    void clear(){
        index_cache.clear();
        core_index.clear();
        delete table;

        opensmt_reset(ctx);
        //opensmt_del_context(ctx);
        ctx = opensmt_mk_context(qf_nra);
        opensmt_set_precision(ctx, precision);
    }
public:
    UnlinearVerify(){
        opensmt_init();
        ctx = opensmt_mk_context(qf_nra);
        table=NULL;
        time=0;
    }
    UnlinearVerify(double pre, DebugInfo *d, int mode){
        opensmt_init();
        ctx = opensmt_mk_context(qf_nra);
        table=NULL;
        this->precision = pre;
        opensmt_set_precision(ctx, pre);
        this->dbg = d;
        this->outMode = mode;
        time=0;
    }
    void setPrecision(double pre){
        this->precision = pre;
        opensmt_set_precision(ctx, pre);
    }
    void setDebugInfo(DebugInfo *dbg){
        this->dbg = dbg;
    }
    void setOutMode(int output){
        this->outMode = output;
    }
    bool check(CFG* ha, vector<int> path);
    vector<IndexPair> get_core_index(){return core_index;}
    ~UnlinearVerify(){delete table; opensmt_del_context(ctx);index_cache.clear();core_index.clear();}
    void print_sol(CFG* cfg);

    double getTime(){return time;}
};



#endif

