#include "UnlinearVerify.h"
#include "time.h"
#include "float.h"
using namespace std;

/***********************  Class UnlinearVarTable  *********************/

    UnlinearVarTable::UnlinearVarTable(opensmt_context &c, CFG *ha):ctx(c), cfg(ha){
        unsigned inputID=0;
        var_num = 0;
        alloca_num = 0;
//        for(int i=0; i<cfg->mainInput.size();i++)
//            errs()<<"UnlinearVarTable initial "<<cfg->mainInput[i]<<"\t"<<cfg->variableList[cfg->mainInput[i]].name<<"\n";
        for(unsigned i=0;i<cfg->variableList.size();i++)
        {
            Variable var =  cfg->variableList[i];
            VarType type = var.type;

            if(inputID<cfg->mainInput.size()&&cfg->mainInput[inputID]==(int)i){

                if(type==FP)
                    x.push_back(opensmt_mk_real_var(ctx, var.name.c_str(), -100.0, 100.0));
//                x.push_back(opensmt_mk_unbounded_real_var(ctx, var.name.c_str()));
                else if(type==INT)
                    x.push_back(opensmt_mk_int_var(ctx, var.name.c_str(), -100.0, 100.0));
                exprMap[i] = var_num;
//                double const x_lb = opensmt_get_lb(ctx, x[var_num]);
//                double const x_ub = opensmt_get_ub(ctx, x[var_num]);
//                errs()<<var.name<<" = ["<<x_lb<<", "<<x_ub<<"]\n";
                inputID++;
                var_num++;
            }
            else if(type==FP){
                x.push_back(opensmt_mk_unbounded_real_var(ctx, var.name.c_str()));
                exprMap[i] = var_num; 
                var_num++;
            }
            else if(type==INT){
                x.push_back(opensmt_mk_unbounded_int_var(ctx, var.name.c_str()));
                exprMap[i] = var_num; 
                var_num++;
            }
        }
    }

    UnlinearVarTable::~UnlinearVarTable(){varVal.clear();alias.clear();storeMap.clear();exprMap.clear();x.clear();var_num=0;alloca_num=0;cfg=NULL;}


    void UnlinearVarTable::setX(int ID, int time, VarType type){
        int ID2 = exprMap[ID];
        if(type==FP)
            x[ID2] = opensmt_mk_unbounded_real_var(ctx, (cfg->variableList[ID].name+"_"+int2string(time)).c_str());
        else if(type==INT)
            x[ID2] = opensmt_mk_unbounded_int_var(ctx, (cfg->variableList[ID].name+"_"+int2string(time)).c_str());
        else
            errs()<<"SetX error 10086!!\n";
    }
    int UnlinearVarTable::alloca(){
        storeMap[++alloca_num] = -2;
        return alloca_num;
    }
    void UnlinearVarTable::setAlias(int ID1, int ID2){
        alias[ID1] = ID2;
    }
    void UnlinearVarTable::setAlias(Variable *v1, Variable *v2){
        int ID1=v1->ID;
        int ID2=v2->ID;
        alias[ID1] = ID2;
    }
    void UnlinearVarTable::setVal(int ID, double val){
        varVal[ID] = val;
    }
    void UnlinearVarTable::store(int ID1, int ID2){
        storeMap[ID1] = ID2;
    }

    int UnlinearVarTable::getNum(){
        return var_num;    
    }
    
    opensmt_expr UnlinearVarTable::getX(int ID){
        int ID2 = exprMap[ID];
        return x[ID2];
    }
    int UnlinearVarTable::load(int ID){
        int count = storeMap.count(ID);
        int storeID;
        if(count){
            storeID = storeMap[ID];
            if(storeID==-2){
                errs()<<"GetLoad error1 "<<ID<<"\t"<<cfg->variableList[ID]<<"\n";
                assert(false);
            }
            return storeID;
        }
        else{
            //errs()<<"GetLoad error2 "<<ID<<"\t"<<cfg->variableList[ID]<<"\n";
            return -1;
        }
    }
    bool UnlinearVarTable::hasAlias(Variable *v){
        int ID = v->ID;
        int count = alias.count(ID);
        if(count)
            return true;
        else
            return false;
    }

    Variable* UnlinearVarTable::getAlias(int ID){
        int count = alias.count(ID);
        int aliasID;
        if(count){
            aliasID = alias[ID];
        }
        else{
            aliasID = ID;
        }
        return &cfg->variableList[aliasID];
    }

    Variable* UnlinearVarTable::getAlias(Variable* var){
        if(var->type==NUM)
            return var;
        int ID = var->ID;
        int count = alias.count(ID);
        int aliasID;
        if(count){
            aliasID = alias[ID];
        }
        else{
            aliasID = ID;
        }
        return &cfg->variableList[aliasID];
    }
    bool UnlinearVarTable::getVal(Variable *var, double &v){
        if(var->type==NUM){
            v=ConvertToDouble(var->name);
            return true;
        }
        int ID = var->ID;
        int count = varVal.count(ID);
        if(count){
            v = varVal[ID];
            return true;
        }
        else{
            return false;
        }
    }
    bool UnlinearVarTable::getVal(int ID, double &v){
        int count = varVal.count(ID);
        if(count){
            v = varVal[ID];
            return true;
        }
        else{
            return false;
        }
    }
    map<int, double> UnlinearVarTable::getValmap(){
           return varVal;
    }
    map<int, int> UnlinearVarTable::getAliasmap(){
           return alias;
    }
    CFG *UnlinearVarTable::getCFG(){
        return cfg;
    }


/****************** Class UnlinearVerify ******************/

/***********************************check with dReal*********************************************/

bool UnlinearVerify::check(CFG* ha, vector<int> path)
{
    clear();

    if(outMode==1)
        printPath(ha, path);
    
    int state_num=(path.size()+1)/2;
    clock_t start,finish;

//    double pre = opensmt_get_precision(ctx);
//    cerr<<"Precision is "<<pre<<endl;

    encode_path(ha, path);

    start = clock();
//    opensmt_use_polytope(ctx);

    bool res = analyze_unsat_core(state_num-1);

    finish=clock();

    time = 1000*(double)(finish-start)/CLOCKS_PER_SEC;
//        errs()<<"Time:\t"<<ConvertToString(time_used)<<"ms\n";
    if(res == true){
        if(outMode==1)
            cerr<<"opensmt_result is sat\n\n\n";
        return true;
    }
    if(outMode==1)
        cerr<<"opensmt_result is unsat\n\n\n";
    return false;
}

void UnlinearVerify::print_sol(CFG* cfg) {
    vector<int> &x = cfg->mainInput;
    for(unsigned i=0;i<x.size();i++){

        opensmt_expr mainInput = table->getX(x[i]);

        double const x_lb = opensmt_get_lb(ctx, mainInput);
        double const x_ub = opensmt_get_ub(ctx, mainInput);
        errs()<<cfg->variableList[x[i]].name<<" = ["<<x_lb<<", "<<x_ub<<"]\n";
    }
    return;
}

opensmt_expr UnlinearVerify::getExpr(Variable *v, bool &treat, double &val, UnlinearVarTable *table)
{
    opensmt_expr expr=NULL;
    if(v->type==NUM){
        expr = opensmt_mk_num_from_string(ctx, v->name.c_str());
        val = ConvertToDouble(v->name);
    }
    else if(v->type == INT || v->type==FP){
        expr = table->getX(v->ID);
        treat = treat&table->getVal(v->ID, val);
    }
    else
        errs()<<"getExpr error : v->type error\n";
    return expr;
}

opensmt_expr UnlinearVerify::opensmt_mk_AND(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num){
    opensmt_expr* xlt = new opensmt_expr[num];
    opensmt_expr* xrt = new opensmt_expr[num];
    opensmt_expr* xt = new opensmt_expr[num];
    vector<opensmt_expr> xl;
    vector<opensmt_expr> xr;

    for(unsigned i=0;i<num;i++){
        string lname = name+"_l"+ConvertToString(i);
        xl.push_back(opensmt_mk_int_var(ctx, lname.c_str(), 0, 1));
        xlt[i] = opensmt_mk_times_2(ctx, xl[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_l = opensmt_mk_eq(ctx, y, opensmt_mk_plus(ctx, xlt, num));
    if(outMode==1){
        opensmt_print_expr(ast_l);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_l);

    for(unsigned i=0;i<num;i++){
        string rname = name+"_r"+ConvertToString(i);
        xr.push_back(opensmt_mk_int_var(ctx, rname.c_str(), 0, 1));
        xrt[i] = opensmt_mk_times_2(ctx, xr[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_r = opensmt_mk_eq(ctx, z, opensmt_mk_plus(ctx, xrt, num));
    if(outMode==1){
        opensmt_print_expr(ast_r);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_r);

    for(unsigned i=0; i<num; i++){
        xt[i] = opensmt_mk_times_2(ctx, opensmt_mk_times_2(ctx, xl[i], xr[i]), opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }

    opensmt_expr ast = opensmt_mk_plus(ctx, xt, num);
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_NAND(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num){
    opensmt_expr* xlt = new opensmt_expr[num];
    opensmt_expr* xrt = new opensmt_expr[num];
    opensmt_expr* xt = new opensmt_expr[num];
    vector<opensmt_expr> xl;
    vector<opensmt_expr> xr;

    for(unsigned i=0;i<num;i++){
        string lname = name+"_l"+ConvertToString(i);
        xl.push_back(opensmt_mk_int_var(ctx, lname.c_str(), 0, 1));
        xlt[i] = opensmt_mk_times_2(ctx, xl[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_l = opensmt_mk_eq(ctx, y, opensmt_mk_plus(ctx, xlt, num));
    if(outMode==1){
        opensmt_print_expr(ast_l);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_l);

    for(unsigned i=0;i<num;i++){
        string rname = name+"_r"+ConvertToString(i);
        xr.push_back(opensmt_mk_int_var(ctx, rname.c_str(), 0, 1));
        xrt[i] = opensmt_mk_times_2(ctx, xr[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_r = opensmt_mk_eq(ctx, z, opensmt_mk_plus(ctx, xrt, num));
    if(outMode==1){
        opensmt_print_expr(ast_r);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_r);

    for(unsigned i=0; i<num; i++){
        xt[i] = opensmt_mk_times_2(ctx, opensmt_mk_minus(ctx, opensmt_mk_num(ctx, 1), opensmt_mk_times_2(ctx, xl[i], xr[i])), opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }

    opensmt_expr ast = opensmt_mk_plus(ctx, xt, num);
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_OR(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num){
    opensmt_expr* xlt = new opensmt_expr[num];
    opensmt_expr* xrt = new opensmt_expr[num];
    opensmt_expr* xt = new opensmt_expr[num];
    vector<opensmt_expr> xl;
    vector<opensmt_expr> xr;

    for(unsigned i=0;i<num;i++){
        string lname = name+"_l"+ConvertToString(i);
        xl.push_back(opensmt_mk_int_var(ctx, lname.c_str(), 0, 1));
        xlt[i] = opensmt_mk_times_2(ctx, xl[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_l = opensmt_mk_eq(ctx, y, opensmt_mk_plus(ctx, xlt, num));
    if(outMode==1){
        opensmt_print_expr(ast_l);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_l);

    for(unsigned i=0;i<num;i++){
        string rname = name+"_r"+ConvertToString(i);
        xr.push_back(opensmt_mk_int_var(ctx, rname.c_str(), 0, 1));
        xrt[i] = opensmt_mk_times_2(ctx, xr[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_r = opensmt_mk_eq(ctx, z, opensmt_mk_plus(ctx, xrt, num));
    if(outMode==1){
        opensmt_print_expr(ast_r);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_r);

    for(unsigned i=0; i<num; i++){
        opensmt_expr xl_t = opensmt_mk_minus(ctx, opensmt_mk_num(ctx, 1), xl[i]);
        opensmt_expr xr_t = opensmt_mk_minus(ctx, opensmt_mk_num(ctx, 1), xr[i]);
        xt[i] = opensmt_mk_times_2(ctx, opensmt_mk_minus(ctx, opensmt_mk_num(ctx, 1), opensmt_mk_times_2(ctx, xl_t, xr_t)), opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }

    opensmt_expr ast = opensmt_mk_plus(ctx, xt, num);
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_XOR(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name, unsigned num){
    opensmt_expr* xlt = new opensmt_expr[num];
    opensmt_expr* xrt = new opensmt_expr[num];
    opensmt_expr* xt = new opensmt_expr[num];
    vector<opensmt_expr> xl;
    vector<opensmt_expr> xr;

    for(unsigned i=0;i<num;i++){
        string lname = name+"_l"+ConvertToString(i);
        xl.push_back(opensmt_mk_int_var(ctx, lname.c_str(), 0, 1));
        xlt[i] = opensmt_mk_times_2(ctx, xl[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_l = opensmt_mk_eq(ctx, y, opensmt_mk_plus(ctx, xlt, num));
    if(outMode==1){
        opensmt_print_expr(ast_l);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_l);

    for(unsigned i=0;i<num;i++){
        string rname = name+"_r"+ConvertToString(i);
        xr.push_back(opensmt_mk_int_var(ctx, rname.c_str(), 0, 1));
        xrt[i] = opensmt_mk_times_2(ctx, xr[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_r = opensmt_mk_eq(ctx, z, opensmt_mk_plus(ctx, xrt, num));
    if(outMode==1){
        opensmt_print_expr(ast_r);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_r);

    for(unsigned i=0; i<num; i++){
        opensmt_expr ite = opensmt_mk_ite(ctx, opensmt_mk_eq(ctx, xl[i], xr[i]), opensmt_mk_num(ctx, 0), opensmt_mk_num(ctx, 1));
        xt[i] = opensmt_mk_times_2(ctx, ite, opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }

    opensmt_expr ast = opensmt_mk_plus(ctx, xt, num);
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_SREM(opensmt_context ctx, opensmt_expr y, opensmt_expr z, string name){
    string div_name = name+"_div";
    string real_name = name+"_divreal";
    opensmt_expr div_real = opensmt_mk_unbounded_real_var(ctx, real_name.c_str());
    opensmt_expr div_expr = opensmt_mk_unbounded_int_var(ctx, div_name.c_str());
    opensmt_expr ast_t = opensmt_mk_eq(ctx, div_real, opensmt_mk_div(ctx, y, z));
    if(outMode==1){
        opensmt_print_expr(ast_t);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_t);

    opensmt_expr ast_tleq = opensmt_mk_leq(ctx, div_expr, div_real);
    opensmt_expr ast_tgt = opensmt_mk_gt(ctx, div_expr, opensmt_mk_minus(ctx, div_real, opensmt_mk_num(ctx, 1)));
    opensmt_expr ast_and = opensmt_mk_and_2(ctx, ast_tleq, ast_tgt);
    if(outMode==1){
        opensmt_print_expr(ast_and);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_and);

    opensmt_expr ast = opensmt_mk_minus(ctx, y, opensmt_mk_times_2(ctx, div_expr, z));
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_ASHR(opensmt_context ctx, opensmt_expr y, int rr, string name, unsigned num){
    opensmt_expr* xt = new opensmt_expr[num];
    vector<opensmt_expr> x;

    for(unsigned i=0;i<num;i++){
        string tname = name+"_t"+ConvertToString(i);
        x.push_back(opensmt_mk_int_var(ctx, tname.c_str(), 0, 1));
        xt[i] = opensmt_mk_times_2(ctx, x[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_t = opensmt_mk_eq(ctx, y, opensmt_mk_plus(ctx, xt, num));
    if(outMode==1){
        opensmt_print_expr(ast_t);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_t);

    delete xt;
    xt = new opensmt_expr[num-rr];
    for(unsigned i=0; i<num-rr; i++){
        xt[i] = opensmt_mk_times_2(ctx, x[i+rr], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }

    opensmt_expr ast = opensmt_mk_plus(ctx, xt, num-rr);
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_SHL(opensmt_context ctx, opensmt_expr y, int rr, string name, unsigned num){
    opensmt_expr* xt = new opensmt_expr[num];
    vector<opensmt_expr> x;

    for(unsigned i=0;i<num;i++){
        string tname = name+"_t"+ConvertToString(i);
        x.push_back(opensmt_mk_int_var(ctx, tname.c_str(), 0, 1));
        xt[i] = opensmt_mk_times_2(ctx, x[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i)));
    }
    opensmt_expr ast_t = opensmt_mk_eq(ctx, y, opensmt_mk_plus(ctx, xt, num));
    
    if(outMode==1){
        opensmt_print_expr(ast_t);
        cerr<< endl;
    }
    opensmt_assert(ctx, ast_t);

    delete xt;
    xt = new opensmt_expr[num-rr];
    for(unsigned i=0; i<num-rr; i++){
        xt[i] = opensmt_mk_times_2(ctx, x[i], opensmt_mk_pow(ctx, opensmt_mk_num(ctx, 2), opensmt_mk_num(ctx, i+rr)));
    }

    opensmt_expr ast = opensmt_mk_plus(ctx, xt, num-rr);
    return ast;
}

opensmt_expr UnlinearVerify::opensmt_mk_INT_cmp(opensmt_context ctx, opensmt_expr x, opensmt_expr y, opensmt_expr z, Op_m pvop, string name){
    opensmt_expr cmp;
    switch(pvop){
        case lt:cmp = opensmt_mk_lt(ctx, y, z);break;
        case le:cmp = opensmt_mk_leq(ctx, y, z);break;
        case gt:cmp = opensmt_mk_gt(ctx, y, z);break;
        case ge:cmp = opensmt_mk_geq(ctx, y, z);break;
        case eq:cmp = opensmt_mk_eq(ctx, y, z);break;
        case ne:cmp = opensmt_mk_not(ctx, opensmt_mk_eq(ctx, y, z));break;
        default:errs()<<"UnlinearVerify::opensmt_mk_INT_cmp error\n";
    }
    opensmt_expr assign = opensmt_mk_ite(ctx, cmp, opensmt_mk_eq(ctx, x, opensmt_mk_num(ctx, 1)), opensmt_mk_eq(ctx, x, opensmt_mk_num(ctx, 0)));
    
    return assign;
}

int UnlinearVerify::getCMP(int rl, int rr, Op_m pvop){
    bool cmp;
    switch(pvop){
        case lt:cmp = (rl<rr);break;
        case le:cmp = (rl<=rr);break;
        case gt:cmp = (rl>rr);break;
        case ge:cmp = (rl>=rr);break;
        case eq:cmp = (rl==rr);break;
        case ne:cmp = (rl!=rr);break;
        default:errs()<<"UnlinearVerify::getCMP error\n";
    }
    if(cmp)
        return 1;
    return 0;
}

opensmt_expr UnlinearVerify::tran_constraint(Constraint *con, UnlinearVarTable *table, int time)
{
    dbg->getConsInfo(con);
    Operator op = con->op;
    
    opensmt_expr exprl; 
    opensmt_expr exprr;
    opensmt_expr ast; 
    
    CFG *cfg = table->getCFG();

    ParaVariable lpv,rpv;
    Variable *lv;
    Variable *rv;
    int ID1,ID2;

    switch(op){
        case LT:
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp1\n";
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.LT GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.LT GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = opensmt_mk_num(ctx, lval);
                exprr = opensmt_mk_num(ctx, rval);
            }
            else{
                if(lv->type==NUM){
                    exprl = opensmt_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==NUM){
                    exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = opensmt_mk_lt(ctx, exprl, exprr);
            break;
        case LE:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp2\n";
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.LE GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.LE GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = opensmt_mk_num(ctx, lval);
                exprr = opensmt_mk_num(ctx, rval);
            }
            else{
                if(lv->type==NUM){
                    exprl = opensmt_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==NUM){
                    exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = opensmt_mk_leq(ctx, exprl, exprr);
            break;
        case GT:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp3\n";
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.GT GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.GT GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = opensmt_mk_num(ctx, lval);
                exprr = opensmt_mk_num(ctx, rval);
            }
            else{
                if(lv->type==NUM){
                    exprl = opensmt_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==NUM){
                    exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = opensmt_mk_gt(ctx, exprl, exprr);
            break;
        case GE:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp4\n";    
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.GE GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.GE GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = opensmt_mk_num(ctx, lval);
                exprr = opensmt_mk_num(ctx, rval);
            }
            else{
                if(lv->type==NUM){
                    exprl = opensmt_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==NUM){
                    exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = opensmt_mk_geq(ctx, exprl, exprr);
            break;
        case EQ:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp5\n";    
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.EQ GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.EQ GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = opensmt_mk_num(ctx, lval);
                exprr = opensmt_mk_num(ctx, rval);
            }
            else{
                if(lv->type==NUM){
                    exprl = opensmt_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==NUM){
                    exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }
            ast = opensmt_mk_eq(ctx, exprl, exprr);
            break;
        case NE:    
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp||rpv.isExp)
                errs()<<"get_constraint error: isExp5\n";    
            lv = table->getAlias(lpv.rvar);
            rv = table->getAlias(rpv.rvar);
            if((lv->type==PTR&&rv->type!=PTR)||(rv->type==PTR&&lv->type!=PTR))
                errs()<<"get_constraint error: Type is diff\n";
            ID1 = lv->ID;
            ID2 = rv->ID;
            
            if(lv->type == PTR){
                double lval,rval;
                if(!table->getVal(ID1,lval))
                    errs()<<"0.NE GetVal error "<<ID1<<"\t"<<cfg->variableList[ID1].name<<"\n";
                if(!table->getVal(ID2,rval))
                    errs()<<"1.NE GetVal error "<<ID2<<"\t"<<cfg->variableList[ID2].name<<"\n";
                exprl = opensmt_mk_num(ctx, lval);
                exprr = opensmt_mk_num(ctx, rval);
            }
            else{
                if(lv->type==NUM){
                    exprl = opensmt_mk_num_from_string(ctx, lv->name.c_str());
                }
                else
                    exprl = table->getX(ID1);
                if(rv->type==NUM){
                    exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                }
                else
                    exprr = table->getX(ID2);
            }        
            ast = opensmt_mk_not(ctx, opensmt_mk_eq(ctx, exprl, exprr));
            break;
        case ASSIGN:{
            lpv = con->lpvList;
            rpv = con->rpvList;
            if(lpv.isExp)
                errs()<<"get_constraint error: isExp6\n";
            lv = table->getAlias(lpv.rvar);
            
            if(lv->type==PTR){
                if(!rpv.isExp){
                    rv = table->getAlias(rpv.rvar);
                    if(rv->type==PTR){
                        table->setAlias(lv, rv);
                    }
                    else
                        errs()<<"get_constraint error: PTR rv->type error1\n";
                }
                else{
                    Op_m pvop = rpv.op;
                    Variable *rvr;
                    double rvrval,val;
                    int allocaID,addr,aliasID;
                    switch(pvop){
                        case GETPTR:
                            rv = table->getAlias(rpv.varList[0]);
                            aliasID = rv->ID;
                            for(unsigned i=1;i<rpv.varList.size()-1;i++){
                                rv = table->getAlias(rpv.varList[i]);
                                if(table->getVal(rv, val)){
                                    aliasID+=val;
                                    if(!table->getVal(aliasID, val)&&outMode==1)
                                        errs()<<"0. Verifi GETPTR error "<<*con<<"\t"<<aliasID<<"\t"<<cfg->variableList[aliasID]<<"\n";
                                    aliasID = val;
                                }
                                else
                                    errs()<<"1. Verifi GETPTR error "<<*con<<"\t"<<rv->ID<<"\n";
                            }
                            rv = table->getAlias(rpv.varList.back());
                            if(table->getVal(rv, val)){
                                aliasID+=val;
                                table->setAlias(lv->ID, aliasID);
                            }
                            else if(outMode==1)
                                errs()<<"2. Verifi GETPTR error "<<*con<<"\t"<<rv->ID<<"\n";
                            break;
                        case ADDR:
                            rv = table->getAlias(rpv.rvar);
                            table->setVal(lv->ID, rv->ID);
                            if(!table->getVal(lv->ID,rvrval)&&outMode==1)
                                errs()<<"Verifi ADDR error "<<*con<<"\t"<<rv->ID<<"\n";
                            break;
                        case STORE:
                            if(!table->getVal(lv->ID, val)&&outMode==1)
                                errs()<<"Verifi store error "<<lv->ID<<"\t"<<lv->name<<"\n";
                            allocaID = (int)val;
                            rv = table->getAlias(rpv.rvar);
                            table->store(allocaID, rv->ID);
                            break;
                        case LOAD:
                            rv = table->getAlias(rpv.rvar);
                            if(!table->getVal(rv->ID, val)&&outMode==1)
                                errs()<<"0.LOAD GetVal error "<<rv->ID<<"\t"<<cfg->variableList[rv->ID].name<<"\n";    
//
                            allocaID = (int)val;
//                            errs()<<"0.2 LOAD : "<<*con<<"\n";
                            addr = table->load(allocaID);
                            if(addr>=0){
                                rvr = table->getAlias(addr);
                                table->setAlias(lv->ID, rvr->ID);
                            }
                            break;
                        case ALLOCA:
                            allocaID = table->alloca();
                            table->setVal(lv->ID, allocaID);
                            break;
                        default:    
                            errs()<<"get_constraint error: PTR rpv.op error "<<*con<<"\n";
                    }
                }
                return NULL;
            }
            else if(lv->type==INT||lv->type==FP){
                if(time>1)
                    table->setX(lv->ID, time, lv->type);
                exprl = table->getX(lv->ID);

                if(!rpv.isExp){
                    rv = table->getAlias(rpv.rvar);
                    if(rv->type==NUM){
                        exprr = opensmt_mk_num_from_string(ctx, rv->name.c_str());
                        double val = ConvertToDouble(rv->name);
                        table->setVal(lv->ID, val);
                    }
                    else if(rv->type==INT || rv->type==FP){
                        exprr = table->getX(rv->ID);
                        double val;
                        if(lv->type==INT && rv->type==FP){
                            opensmt_expr ast_tleq = opensmt_mk_leq(ctx, exprl, exprr);
                            opensmt_expr ast_tgt = opensmt_mk_gt(ctx, exprl, opensmt_mk_minus(ctx, exprr, opensmt_mk_num(ctx, 1)));
                            opensmt_expr ast_and = opensmt_mk_and_2(ctx, ast_tleq, ast_tgt);
                            
                            if(table->getVal(rv->ID, val))
                                table->setVal(lv->ID, (int)val);
                            return ast_and;
                        }
                        else{
                            if(table->getVal(rv->ID, val))
                                table->setVal(lv->ID, val);
                        }
                    }
                    else
                        errs()<<"get_constraint error: DATA rv->type error\n";
                }
                else{
                    Op_m pvop = rpv.op;
                    Variable *rvl;
                    Variable *rvr;
                    double rl=0;
                    double rr=0;
                    double val=0;
                    opensmt_expr y;
                    opensmt_expr z;
                    string name = lv->name;
                    bool treat = true;
                    switch(pvop){
                        case LOAD:
                            rvr = table->getAlias(rpv.rvar);
                            if(!table->getVal(rvr->ID, val)&&outMode==1)
                                errs()<<"2.LOAD GetVal error "<<rvr->ID<<"\t"<<cfg->variableList[rvr->ID].name<<"\n";    
                            rl = (int)val;
                            rr = table->load(rl);
                            treat = table->getVal(rr, val);
                            if(treat)
                                table->setVal(lv->ID, val);
                            exprr = table->getX(rr);
                            break;
                        case AND:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);        
                            exprr = opensmt_mk_AND(ctx, y, z, name, 32);    
                            if(treat)
                                table->setVal(lv->ID, (int)rl&(int)rr);
                            break;
                        case NAND:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_NAND(ctx, y, z, name, 32);
                            if(treat)
                                table->setVal(lv->ID, ~((int)rl&(int)rr));
                            break;
                        case OR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_OR(ctx, y, z, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl|(int)rr);
                            break;
                        case XOR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_XOR(ctx, y, z, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl^(int)rr);
                            break;
                        case SREM:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_SREM(ctx, y, z, name);
                            if(treat)
                                table->setVal(lv->ID, (int)rl%(int)rr);
                            break;
                        case ASHR:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            if(!treat)
                                errs()<<"ASHR error: invalid z value\n";
                            y = getExpr(rvl, treat, rl, table);
                            if(rr<0)
                                exprr = opensmt_mk_SHL(ctx, y, -(int)rr, name, 32);
                            else
                                exprr = opensmt_mk_ASHR(ctx, y, (int)rr, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl>>(int)rr);
                            break;
                        case SHL:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            if(!treat)
                                errs()<<"SHL error: invalid z value\n";
                            y = getExpr(rvl, treat, rl, table);
                            if(rr>=0)
                                exprr = opensmt_mk_SHL(ctx, y, (int)rr, name, 32);
                            else
                                exprr = opensmt_mk_ASHR(ctx, y, -(int)rr, name, 32);
                            if(treat)
                                table->setVal(lv->ID, (int)rl<<(int)rr);
                            break;
                        case ADD:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_plus_2(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, rl+rr);
                            break;
                        case SUB:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_minus(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, rl-rr);
                            break;
                        case TAN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_tan(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, tan(rr));
                            break;
                        case ATAN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_atan(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, atan(rr));
                            break;
                        case ATAN2:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_atan2(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, atan2(rl, rr));
                            break;
                        case SIN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_sin(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, sin(rr));
                            break;
                        case ASIN:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_asin(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, asin(rr));
                            break;
                        case COS:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_cos(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, cos(rr));
                            break;
                        case ACOS:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_acos(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, acos(rr));
                            break;
                        case SQRT:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_pow(ctx, z, opensmt_mk_num(ctx, 0.5));
                            if(treat)
                                table->setVal(lv->ID, sqrt(rr));
                            break;
                        case POW:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_pow(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, powf(rl,rr));
                            break;
                        case LOG:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_log(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, log(rr));
                            break;
                        case LOG10:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_div(ctx, opensmt_mk_log(ctx, z),opensmt_mk_log(ctx, opensmt_mk_num(ctx, 10)));
                            if(treat)
                                table->setVal(lv->ID, log10(rr));
                            break;
                        case ABS:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_abs(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, fabs(rr));
                            break;
                        case EXP:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_exp(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, exp(rr));
                            break;
                        case SINH:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_sinh(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, sinh(rr));
                            break;
                        case COSH:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_cosh(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, cosh(rr));
                            break;
                        case TANH:
                            rvr = rpv.rvar;
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_tanh(ctx, z);
                            if(treat)
                                table->setVal(lv->ID, tanh(rr));
                            break;
                        case MUL:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_times_2(ctx, y, z);
                            if(treat)
                                table->setVal(lv->ID, rl*rr);
                            break;
                        case DIV:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            exprr = opensmt_mk_div(ctx, y, z);
                            if(treat&&rr!=0)
                                table->setVal(lv->ID, rl/rr);
                            break;
                        case lt:case le:case gt:case ge:case eq:case ne:
                            rvl = rpv.lvar;
                            rvr = rpv.rvar;
                            y = getExpr(rvl, treat, rl, table);
                            z = getExpr(rvr, treat, rr, table);
                            ast = opensmt_mk_INT_cmp(ctx, exprl, y, z, pvop, name);
                            if(treat)
                                table->setVal(lv->ID, getCMP(rl, rr ,pvop));
                            return ast;
                            break;
                        default:
                            errs()<<"get_constraint error: DATA rpv.op error "<<*con<<"\n";
                    }
                }
            }
            else
                errs()<<"get_constraint error: lv->type error\n";
            ast = opensmt_mk_eq(ctx, exprl, exprr);
            break;
        }
    }

    return ast;

}

void UnlinearVerify::get_constraint(vector<Constraint> consList, UnlinearVarTable *table, int time, bool isTransition){
   
    /* 
    unsigned size = consList.size();
    
    bool isOR = (isTransition && size>1);
    opensmt_expr *cons=NULL;
    if(isOR)
        cons = new opensmt_expr[size];
    */

    for(unsigned m=0;m<consList.size();m++)
    {
        Constraint* con = &consList[m];
        opensmt_expr ast = tran_constraint(con, table, time );

        if(ast!=NULL){
/*
            if(isOR){
                cons[m] = ast;
            }
            else{
                opensmt_print_expr(ast);
                opensmt_assert(ctx, ast);
                cerr<< endl;
            }
*/
            opensmt_assert(ctx, ast);
            if(outMode==1){
                opensmt_print_expr(ast);
                cerr<< endl;
            }
        }
    }
/*
    if(isOR){
        opensmt_expr exprs = opensmt_mk_or(ctx, cons, size);
        opensmt_print_expr(exprs);
        opensmt_assert(ctx, exprs);
        cerr<< endl;
    }
*/
}

void UnlinearVerify::encode_path(CFG* ha, vector<int> patharray)
{
    table = new UnlinearVarTable(ctx, ha);

    int state_num =     (patharray.size()+1)/2;
    int total_state  = ha->stateList.size()+ ha->transitionList.size();
    vector<int> repeat(total_state,0);
    
    for (int j= 0;j<state_num; j++)
    {    
        int ID = patharray[2*j];
        State* st=ha->searchState(ID);
        assert(st!=NULL);
        if(outMode==1)
            cerr<<st->name<<":"<<endl;
        get_constraint(st->consList, table, repeat[ID], false);
        repeat[ID]+=1;
        
        if(j!=state_num-1)    
        {
            ID = patharray[2*j+1];
            Transition* pre=ha->searchTransition(ID);
            assert(pre!=NULL);
            if(outMode==1)
                cerr<<pre->name<<":"<<endl;

            get_constraint(pre->guardList, table, repeat[ID], true);    
            repeat[ID]+=1;

        }
    }
//    cerr<<"Path encode complete~~~~~~~~~~~~~~~~~~ "<<endl;

}

bool UnlinearVerify::analyze_unsat_core(int state){
    opensmt_result res = opensmt_check( ctx );

    if(res == l_true){
        return true;
    }
    else{
        add_IIS(IndexPair(0, state));
        return false;
    }
}

void UnlinearVerify::add_IIS(IndexPair index){
    for(unsigned i=0;i<core_index.size();i++){
        if(index.contain(core_index[i])){
          core_index[i] = index;
          return;
        }
        else if(core_index[i].contain(index))
          return;
    }
    core_index.push_back(index);

}
