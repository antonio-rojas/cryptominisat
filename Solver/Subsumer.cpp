/**************************************************************************************************
From: Solver.C -- (C) Niklas Een, Niklas Sorensson, 2004
**************************************************************************************************/

#include "Solver.h"
#include "Subsumer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "assert.h"
#include <iomanip>
#include "ClauseDumper.h"
#include "VarReplacer.h"
#include "Conglomerate.h"

//#define VERBOSE_DEBUG
#ifdef VERBOSE_DEBUG
#define BIT_MORE_VERBOSITY
#endif

//#define BIT_MORE_VERBOSITY
//#define TOUCH_LESS

#ifdef VERBOSE_DEBUG
using std::cout;
using std::endl;
#endif //VERBOSE_DEBUG

Subsumer::Subsumer(Solver& s):
    occur_mode(occ_Permanent)
    , solver(s)
    , numCalls(0)
    , numElimed(0)
{
};

Subsumer::~Subsumer()
{
}

void Subsumer::extendModel(Solver& solver2)
{
    vec<Lit> tmp;
    typedef map<Var, vector<vector<Lit> > > elimType;
    for (elimType::iterator it = elimedOutVar.begin(), end = elimedOutVar.end(); it != end; it++) {
        Var var = it->first;
        solver2.setDecisionVar(var, true);
        for (vector<vector<Lit> >::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            tmp.clear();
            tmp.growTo(it2->size());
            memcpy(tmp.getData(), it2->data(), sizeof(Lit)*it2->size());
            solver2.addClause(tmp);
        }
    }
}

bool selfSubset(uint32_t A, uint32_t B)
{
    uint32_t B_tmp = B | ((B & 0xAAAAAAAALL) >> 1) | ((B & 0x55555555LL) << 1);
    if ((A & ~B_tmp) == 0){
        uint32_t C = A & ~B;
        return (C & (C-1)) == 0;
    }else
        return false;
}

// Assumes 'seen' is cleared (will leave it cleared)
bool selfSubset(Clause& A, Clause& B, vec<char>& seen)
{
    for (uint32_t i = 0; i < B.size(); i++)
        seen[B[i].toInt()] = 1;
    
    bool    flip = false;
    for (uint32_t i = 0; i < A.size(); i++) {
        if (!seen[A[i].toInt()]) {
            if (flip == true || !seen[(~A[i]).toInt()]) {
                for (uint32_t i = 0; i < B.size(); i++) seen[B[i].toInt()] = 0;
                return false;
            }
            flip = true;
        }
    }
    for (uint32_t i = 0; i < B.size(); i++)
        seen[B[i].toInt()] = 0;
    return flip;
}

// Will put NULL in 'cs' if clause removed.
uint Subsumer::subsume0(Clause& ps)
{
    uint retIndex = UINT_MAX;
    #ifdef VERBOSE_DEBUG
    cout << "subsume0 orig clause:";
    ps.clause->plainPrint();
    cout << "pointer:" << ps.clause << endl;
    #endif
    
    vec<ClauseSimp> subs;
    findSubsumed(ps, subs);
    for (uint32_t i = 0; i < subs.size(); i++){
        clauses_subsumed++;
        #ifdef VERBOSE_DEBUG
        cout << "subsume0 removing:";
        subs[i].clause->plainPrint();
        #endif
        
        Clause* tmp = subs[i].clause;
        unlinkClause(subs[i]);
        free(tmp);
        retIndex = subs[i].index;
    }
    
    return retIndex;
}

void Subsumer::unlinkClause(ClauseSimp c, Var elim)
{
    Clause& cl = *c.clause;
    
    if (elim != var_Undef) {
        assert(!cl.learnt());
        io_tmp.clear();
        for (int i = 0; i < cl.size(); i++)
            io_tmp.push_back(cl[i]);
        elimedOutVar[elim].push_back(io_tmp);
    }
    
    if (updateOccur(cl)) {
        for (uint32_t i = 0; i < cl.size(); i++) {
            maybeRemove(occur[cl[i].toInt()], &cl);
            #ifndef TOUCH_LESS
            touch(cl[i]);
            #endif
        }
    }
    
    solver.detachClause(cl);
    
    // Remove from iterator vectors/sets:
    for (uint32_t i = 0; i < iter_vecs.size(); i++) {
        vec<ClauseSimp>& cs = *iter_vecs[i];
        for (uint32_t j = 0; j < cs.size(); j++)
            if (cs[j].clause == &cl)
                cs[j].clause = NULL;
    }
    for (uint32_t i = 0; i < iter_sets.size(); i++) {
        CSet& cs = *iter_sets[i];
        cs.exclude(c);
    }
    
    // Remove clause from clause touched set:
    if (updateOccur(cl)) {
        cl_touched.exclude(c);
        cl_added.exclude(c);
    }
    
    clauses[c.index].clause = NULL;
}

void Subsumer::unlinkModifiedClause(vec<Lit>& cl, ClauseSimp c)
{
    if (updateOccur(*c.clause)) {
        for (uint32_t i = 0; i < cl.size(); i++) {
            maybeRemove(occur[cl[i].toInt()], c.clause);
            #ifndef TOUCH_LESS
            touch(cl[i]);
            #endif
        }
    }
    
    solver.detachModifiedClause(cl[0], cl[1], cl.size(), c.clause);
    
    // Remove from iterator vectors/sets:
    for (uint32_t i = 0; i < iter_vecs.size(); i++){
        vec<ClauseSimp>& cs = *iter_vecs[i];
        for (uint32_t j = 0; j < cs.size(); j++)
            if (cs[j].clause == c.clause)
                cs[j].clause = NULL;
    }
    for (uint32_t i = 0; i < iter_sets.size(); i++){
        CSet& cs = *iter_sets[i];
        cs.exclude(c);
    }
    
    // Remove clause from clause touched set:
    if (updateOccur(*c.clause)) {
        cl_touched.exclude(c);
        cl_added.exclude(c);
    }
}

void Subsumer::subsume1(ClauseSimp& ps)
{
    vec<ClauseSimp>    Q;
    vec<ClauseSimp>    subs;
    vec<Lit>        qs;
    uint32_t        q;
    
    registerIteration(Q);
    registerIteration(subs);
    
    Q.push(ps);
    q = 0;
    while (q < Q.size()){
        if (Q[q].clause == NULL) { q++; continue; }
        #ifdef VERBOSE_DEBUG
        cout << "subsume1 orig clause:";
        Q[q].clause->plainPrint();
        #endif
        
        qs.clear();
        for (uint32_t i = 0; i < Q[q].clause->size(); i++)
            qs.push((*Q[q].clause)[i]);
        
        for (uint32_t i = 0; i < qs.size(); i++){
            qs[i] = ~qs[i];
            findSubsumed(qs, subs);
            for (uint32_t j = 0; j < subs.size(); j++){
                /*#ifndef NDEBUG
                if (&counter != NULL && counter == -1){
                    dump(*subs[j].clause);
                    qs[i] = ~qs[i];
                    dump(qs);
                    printf(L_LIT"\n", L_lit(qs[i]));
                    exit(0);
                }
                #endif*/
                if (subs[j].clause == NULL) continue;
                literals_removed++;
                
                #ifdef VERBOSE_DEBUG
                cout << "orig clause    :";
                subs[j].clause->plainPrint();
                #endif
                ClauseSimp c = subs[j];
                Clause& cl = *c.clause;
                unlinkClause(c);
                
                cl.strengthen(qs[i]);
                #ifdef VERBOSE_DEBUG
                cout << "strenghtened   :";
                c.clause->plainPrint();
                #endif
                
                assert(cl.size() > 0);
                if (cl.size() > 1) {
                    updateClause(c);
                    if (c.clause != NULL) {
                        solver.attachClause(cl);
                        Q.push(c);
                    }
                } else {
                    if (solver.assigns[cl[0].var()] == l_Undef) {
                        solver.uncheckedEnqueue(cl[0]);
                        #ifdef VERBOSE_DEBUG
                        cout << "Found that var " << cl[0].var()+1 << " must be " << std::boolalpha << !cl[0].sign() << endl;
                        #endif
                    } else {
                        if (solver.assigns[cl[0].var()].getBool() != !cl[0].sign()) {
                            solver.ok = false;
                            unregisterIteration(Q);
                            unregisterIteration(subs);
                            free(&cl);
                            return;
                        }
                    }
                    free(&cl);
                }
            }
            
            qs[i] = ~qs[i];
            subs.clear();
        }
        q++;
    }
    
    unregisterIteration(Q);
    unregisterIteration(subs);
}

void Subsumer::updateClause(ClauseSimp& c)
{
    if (isSubsumed(*c.clause)) {
        free(c.clause);
        c.clause = NULL;
        return;
    }
    
    linkInAlreadyClause(c);
    cl_touched.add(c);
    
    if (!c.clause->learnt()) subsume0(*c.clause);
}

void Subsumer::almost_all_database()
{
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c Larger database" << std::endl;
    #endif
    // Optimized variant when virtually whole database is involved:
    cl_added  .clear();
    cl_touched.clear();
    
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause != NULL && updateOccur(*clauses[i].clause))
            subsume1(clauses[i]);
    }
    if (!solver.ok) return;
    solver.ok = solver.propagate() == NULL;
    if (!solver.ok) {
        std::cout << "c (contradiction during subsumption)" << std::endl;
        return;
    }
    solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
    
    #ifdef VERBOSE_DEBUG
    cout << "subsume1 part 1 finished" << endl;
    #endif
    
    CSet s1;
    registerIteration(s1);
    while (cl_touched.size() > 0){
        #ifdef VERBOSE_DEBUG
        std::cout << "c cl_touched was > 0, new iteration" << std::endl;
        #endif
        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause != NULL)
                s1.add(*it);
        }
        cl_touched.clear();
        
        for (CSet::iterator it = s1.begin(), end = s1.end(); it != end; ++it) {
            if (it->clause != NULL)
                subsume1(*it);
        }
        s1.clear();
        
        if (!solver.ok) return;
        solver.ok = solver.propagate() == NULL;
        if (!solver.ok) {
            printf("c (contradiction during subsumption)\n");
            unregisterIteration(s1);
            return;
        }
        solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
    }
    unregisterIteration(s1);
    
    printf("c final stage: subsume0\n");
    for (int i = 0; i < clauses.size(); i++) {
        assert(clauses[i].index == i);
        if (clauses[i].clause != NULL)
            subsume0(*clauses[i].clause);
    }
}

void Subsumer::smaller_database()
{
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c Smaller database" << std::endl;
    #endif
    //  Set used in 1-subs:
    //      (1) clauses containing a negated literal of an added clause.
    //      (2) all added or strengthened ("touched") clauses.
    //
    //  Set used in 0-subs:
    //      (1) clauses containing a (non-negated) literal of an added clause, including the added clause itself.
    //      (2) all strenghtened clauses -- REMOVED!! We turned on eager backward subsumption which supersedes this.
    
    #ifdef VERBOSE_DEBUG
    printf("  PREPARING\n");
    #endif
    
    CSet s0, s1;     // 's0' is used for 0-subsumption, 's1' for 1-subsumption
    vec<char>   ol_seen(solver.nVars()*2, 0);
    for (CSet::iterator it = cl_added.begin(), end = cl_added.end(); it != end; ++it) {
        if (it->clause == NULL) continue;
        ClauseSimp& c = *it;
        Clause& cl = *it->clause;
        
        s1.add(c);
        for (uint32_t j = 0; j < cl.size(); j++){
            if (ol_seen[cl[j].toInt()]) continue;
            ol_seen[cl[j].toInt()] = 1;
            
            vec<ClauseSimp>& n_occs = occur[(~cl[j]).toInt()];
            for (uint32_t k = 0; k < n_occs.size(); k++)
                if (n_occs[k].clause != c.clause && n_occs[k].clause->size() <= cl.size() && selfSubset(n_occs[k].clause->getAbst(), c.clause->getAbst()) && selfSubset(*n_occs[k].clause, cl, seen_tmp))
                    s1.add(n_occs[k]);
                
            vec<ClauseSimp>& p_occs = occur[cl[j].toInt()];
            for (uint32_t k = 0; k < p_occs.size(); k++)
                if (subsetAbst(p_occs[k].clause->getAbst(), c.clause->getAbst()))
                    s0.add(p_occs[k]);
        }
    }
    cl_added.clear();
    
    registerIteration(s0);
    registerIteration(s1);
    
    #ifdef VERBOSE_DEBUG
    printf("  FIXED-POINT\n");
    #endif
    
    // Fixed-point for 1-subsumption:
    while (s1.size() > 0 || cl_touched.size() > 0){
        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause != NULL) {
                s1.add(*it);
                s0.add(*it);
            }
        }
        
        cl_touched.clear();
        assert(solver.qhead == solver.trail.size());
        
        #ifdef VERBOSE_DEBUG
        printf("s1.size()=%d  cl_touched.size()=%d\n", s1.size(), cl_touched.size());
        #endif
        
        for (CSet::iterator it = s1.begin(), end = s1.end(); it != end; ++it) {
            if (it->clause != NULL)
                subsume1(*it);
        }
        s1.clear();
        
        if (!solver.ok) return;
        solver.ok = solver.propagate() == NULL;
        if (!solver.ok){
            printf("c (contradiction during subsumption)\n");
            unregisterIteration(s1);
            unregisterIteration(s0);
            return; 
        }
        solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
        assert(cl_added.size() == 0);
    }
    unregisterIteration(s1);
    
    // Iteration pass for 0-subsumption:
    for (CSet::iterator it = s0.begin(), end = s0.end(); it != end; ++it) {
        if (it->clause != NULL)
            subsume0(*it->clause);
    }
    s0.clear();
    unregisterIteration(s0);
}

ClauseSimp Subsumer::linkInClause(Clause& cl)
{
    ClauseSimp c(&cl, clauseID++);
    clauses.push(c);
    if (updateOccur(cl)) {
        for (uint32_t i = 0; i < cl.size(); i++) {
            occur[cl[i].toInt()].push(c);
            touch(cl[i].var());
        }
    }
    cl_added.add(c);
    
    return c;
}

void Subsumer::linkInAlreadyClause(ClauseSimp& c)
{
    Clause& cl = *c.clause;
    
    if (updateOccur(cl)) {
        for (uint32_t i = 0; i < c.clause->size(); i++) {
            occur[cl[i].toInt()].push(c);
            touch(cl[i].var());
        }
    }
    cl_touched.add(c);
}

void Subsumer::addFromSolver(vec<Clause*>& cs)
{
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end = i + cs.size(); i !=  end; i++) {
        if ((*i)->learnt()) {
            *j++ = *i;
            continue;
        }
        ClauseSimp c(*i, clauseID++);
        clauses.push(c);
        Clause& cl = *c.clause;
        if (updateOccur(cl)) {
            for (uint32_t i = 0; i < cl.size(); i++) {
                occur[cl[i].toInt()].push(c);
                touch(cl[i].var());
            }
            if (fullSubsume || cl.getVarChanged()) cl_added.add(c);
            else if (cl.getStrenghtened()) cl_touched.add(c);
            if (cl.getVarChanged() || cl.getStrenghtened())
                cl.calcAbstraction();
        }
    }
    cs.shrink(i-j);
}

void Subsumer::addBackToSolver()
{
    for (uint i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause != NULL) {
            if (clauses[i].clause->size() == 2)
                solver.binaryClauses.push(clauses[i].clause);
            else {
                if (clauses[i].clause->learnt())
                    solver.learnts.push(clauses[i].clause);
                else
                    solver.clauses.push(clauses[i].clause);
            }
            clauses[i].clause->unsetStrenghtened();
            clauses[i].clause->unsetVarChanged();
        }
    }
}

void Subsumer::removeWrong(vec<Clause*>& cs)
{
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end =  i + cs.size(); i != end; i++) {
        Clause& c = **i;
        if (!c.learnt())  {
            *j++ = *i;
            continue;
        }
        bool remove = false;
        for (Lit *l = c.getData(), *end2 = l+c.size(); l != end2; l++) {
            if (var_elimed[l->var()]) {
                remove = true;
                solver.detachClause(c);
                free(&c);
                break;
            }
        }
        if (!remove)
            *j++ = *i;
    }
    cs.shrink(i-j);
}

void Subsumer::fillCannotEliminate()
{
    std::fill(cannot_eliminate.getData(), cannot_eliminate.getData()+cannot_eliminate.size(), false);
    for (uint i = 0; i < solver.xorclauses.size(); i++) {
        const XorClause& c = *solver.xorclauses[i];
        for (uint i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }
    
    const vector<bool>& tmp2 = solver.conglomerate->getRemovedVars();
    for (uint i = 0; i < tmp2.size(); i++) {
        if (tmp2[i]) cannot_eliminate[i] = true;
    }
    
    const vec<Clause*>& tmp = solver.varReplacer->getClauses();
    for (uint i = 0; i < tmp.size(); i++) {
        const Clause& c = *tmp[i];
        for (uint i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }
    
    #ifdef VERBOSE_DEBUG
    uint tmpNum = 0;
    for (uint i = 0; i < cannot_eliminate.size(); i++)
        if (cannot_eliminate[i])
            tmpNum++;
    std::cout << "Cannot eliminate num:" << tmpNum << std::endl;
    #endif
}

const bool Subsumer::simplifyBySubsumption(const bool doFullSubsume)
{
    fullSubsume = doFullSubsume;
    double myTime = cpuTime();
    uint32_t origTrailSize = solver.trail.size();
    clauses_subsumed = 0;
    literals_removed = 0;
    origNClauses = solver.clauses.size() + solver.binaryClauses.size();
    numCalls++;
    clauseID = 0;
    
    touched_list.clear();
    for (Var i = 0; i < solver.nVars(); i++) {
        if (solver.decision_var[i]) touched_list.push(i);
        touched[i] = true;
        occur[2*i].clear(true);
        occur[2*i+1].clear(true);
    }
    
    while (solver.varReplacer->getNewToReplaceVars() > 0) {
        if (solver.performReplace && !solver.varReplacer->performReplace(true))
            return false;
    }
    
    fillCannotEliminate();
    
    clauses.clear();
    cl_added.clear();
    cl_touched.clear();
    
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    addFromSolver(solver.clauses);
    solver.clauseCleaner->cleanClauses(solver.binaryClauses, ClauseCleaner::binaryClauses);
    addFromSolver(solver.binaryClauses);
    uint32_t origNLearnts = solver.learnts.size();
    
    for (uint32_t i = 0; i < clauses.size(); i++) {
        assert(clauses[i].index == i);
        if (clauses[i].clause != NULL
            && (fullSubsume
            || clauses[i].clause->getStrenghtened()
            || clauses[i].clause->getVarChanged())
            )
            subsume0(*clauses[i].clause);
    }
    
    Clause** a = solver.learnts.getData();
    Clause** b = a;
    for (Clause** end = a + solver.learnts.size(); a != end; a++) {
        if ((*a)->getStrenghtened() || (*a)->getVarChanged()) {
            uint index = subsume0(**a);
            if (index != UINT_MAX) {
                (*a)->makeNonLearnt();
                clauses[index].clause = *a;
                linkInAlreadyClause(clauses[index]);
                solver.learnts_literals -= (*a)->size();
                solver.clauses_literals += (*a)->size();
            } else {
                *b++  = *a;
            }
        }
    }
    solver.learnts.shrink(a-b);
    
    //uint32_t    orig_n_clauses  = solver.nClauses();
    //uint32_t    orig_n_literals = solver.nLiterals();
    
    if (!solver.ok) return false;
    #ifdef VERBOSE_DEBUG
    std::cout << "c   pre-subsumed:" << clauses_subsumed << std::endl;
    std::cout << "c   cl_added:" << cl_added.size() << std::endl;
    std::cout << "c   cl_touched:" << cl_touched.size() << std::endl;
    std::cout << "c   clauses:" << clauses.size() << std::endl;
    std::cout << "c   origNClauses:" << origNClauses << std::endl;
    #endif
    
    do{
        // SUBSUMPTION:
        //
        
        if (cl_added.size() > origNClauses / 2) {
            almost_all_database();
            if (!solver.ok) return false;
        } else {
            smaller_database();
            if (!solver.ok) return false;
        }
        
        #ifdef VERBOSE_DEBUG
        printf("c VARIABLE ELIMINIATION\n");
        std::cout << "c toucheds list size:" << touched_list.size() << std::endl;
        #endif
        vec<Var> init_order;
        orderVarsForElim(init_order);   // (will untouch all variables)
        
        for (bool first = true;; first = false){
            int vars_elimed = 0;
            int clauses_before = solver.nClauses();
            vec<Var> order;
            
            if (first) {
                //init_order.copyTo(order);
                for (int i = 0; i < init_order.size(); i++) {
                    if (!var_elimed[init_order[i]] && !cannot_eliminate[init_order[i]] && solver.decision_var[init_order[i]])
                        order.push(init_order[i]);
                }
            } else {
                for (int i = 0; i < touched_list.size(); i++) {
                    if (!var_elimed[touched_list[i]] && !cannot_eliminate[touched_list[i]] && solver.decision_var[touched_list[i]]) {
                        order.push(touched_list[i]);
                        touched[touched_list[i]] = 0;
                    }
                }
                touched_list.clear();
            }
            #ifdef VERBOSE_DEBUG
            std::cout << "Order size:" << order.size() << std::endl;
            #endif
            
            assert(solver.qhead == solver.trail.size());
            for (int i = 0; i < order.size(); i++){
                /*#ifndef SAT_LIVE
                if (i % 1000 == 999 || i == order.size()-1)
                    printf("  -- var.elim.:  %d/%d          \n", i+1, order.size());
                #endif*/
                if (maybeEliminate(order[i])){
                    vars_elimed++;
                    solver.ok = solver.propagate() == NULL;
                    if (!solver.ok) {
                        printf("c (contradiction during subsumption)\n");
                        return false;
                    }
                }
            }
            assert(solver.qhead == solver.trail.size());
            
            if (vars_elimed == 0)
                break;
            
            printf("c  #clauses-removed: %-8d #var-elim: %d\n", clauses_before - solver.nClauses(), vars_elimed);
            
        }
    }while (cl_added.size() > 100);
    
    if (!solver.ok) return false;
    solver.ok = (solver.propagate() == NULL);
    if (!solver.ok) {
        printf("c (contradiction during subsumption)\n");
        return false;
    }
    
    if (solver.trail.size() - origTrailSize > 0)
        solver.order_heap.filter(Solver::VarFilter(solver));
    
    addBackToSolver();
    removeWrong(solver.learnts);
    removeWrong(solver.binaryClauses);
    solver.nbCompensateSubsumer += origNLearnts-solver.learnts.size();
    
    std::cout << "c |  literals-removed: " << std::setw(9) << literals_removed
    << " clauses-subsumed: " << std::setw(9) << clauses_subsumed
    << " vars fixed: " << std::setw(3) <<solver.trail.size() - origTrailSize
    << " time: " << std::setw(5) << std::setprecision(2) << (cpuTime() - myTime)
    << "  |" << std::endl;
    
    return true;
}

void Subsumer::findSubsumed(Clause& ps, vec<ClauseSimp>& out_subsumed)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed: ";
    for (uint i = 0; i < ps.clause->size(); i++) {
        if ((*ps.clause)[i].sign()) printf("-");
        printf("%d ", (*ps.clause)[i].var() + 1);
    }
    printf("0\n");
    #endif
    
    int min_i = 0;
    for (uint32_t i = 1; i < ps.size(); i++){
        if (occur[ps[i].toInt()].size() < occur[ps[min_i].toInt()].size())
            min_i = i;
    }
    
    vec<ClauseSimp>& cs = occur[ps[min_i].toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);
        
        if (it->clause != &ps && subsetAbst(ps.getAbst(), it->clause->getAbst()) && ps.size() <= it->clause->size() && subset(ps, *it->clause, seen_tmp)) {
            out_subsumed.push(*it);
            #ifdef VERBOSE_DEBUG
            cout << "subsumed: ";
            it->clause->plainPrint();
            #endif
        }
    }
}

void Subsumer::findSubsumed(vec<Lit>& ps, vec<ClauseSimp>& out_subsumed)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed: ";
    for (uint i = 0; i < ps.size(); i++) {
        if (ps[i].sign()) printf("-");
        printf("%d ", ps[i].var() + 1);
    }
    printf("0\n");
    #endif
    
    uint32_t abst = calcAbstraction(ps);
    
    uint32_t min_i = 0;
    for (uint32_t i = 1; i < ps.size(); i++){
        if (occur[ps[i].toInt()].size() < occur[ps[min_i].toInt()].size())
            min_i = i;
    }
    
    vec<ClauseSimp>& cs = occur[ps[min_i].toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);
        
        if (subsetAbst(abst, it->clause->getAbst()) && ps.size() <= it->clause->size() && subset(ps, *it->clause, seen_tmp)) {
            out_subsumed.push(*it);
            #ifdef VERBOSE_DEBUG
            cout << "subsumed: ";
            it->clause->plainPrint();
            #endif
        }
    }
}

void inline Subsumer::MigrateToPsNs(vec<ClauseSimp>& poss, vec<ClauseSimp>& negs, vec<ClauseSimp>& ps, vec<ClauseSimp>& ns, const Var x)
{
    poss.moveTo(ps);
    negs.moveTo(ns);
    
    for (int i = 0; i < ps.size(); i++)
        unlinkClause(ps[i], x);
    for (int i = 0; i < ns.size(); i++)
        unlinkClause(ns[i], x);
}

void inline Subsumer::DeallocPsNs(vec<ClauseSimp>& ps, vec<ClauseSimp>& ns)
{
    for (int i = 0; i < ps.size(); i++) {
        clauses[ps[i].index].clause = NULL;
        free(ps[i].clause);
    }
    for (int i = 0; i < ns.size(); i++) {
        clauses[ns[i].index].clause = NULL;
        free(ns[i].clause);
    }
}

// Returns TRUE if variable was eliminated.
bool Subsumer::maybeEliminate(const Var x)
{
    assert(solver.qhead == solver.trail.size());
    assert(!var_elimed[x]);
    assert(!cannot_eliminate[x]);
    assert(solver.decision_var[x]);
    if (solver.value(x) != l_Undef) return false;
    if (occur[Lit(x, false).toInt()].size() == 0 && occur[Lit(x, true).toInt()].size() == 0)
        return false;
    
    vec<ClauseSimp>&   poss = occur[Lit(x, false).toInt()];
    vec<ClauseSimp>&   negs = occur[Lit(x, true).toInt()];
    vec<ClauseSimp>    new_clauses;
    
    int before_clauses  = -1;
    int before_literals = -1;
    
    bool    elimed     = false;
    bool    tried_elim = false;
    
    // Heuristic:
    if (poss.size() >= 8 && negs.size() >= 8)      // <<== CUT OFF
        //  if (poss.size() >= 7 && negs.size() >= 7)      // <<== CUT OFF
        //  if (poss.size() >= 6 && negs.size() >= 6)      // <<== CUT OFF
        return false;
    
    // Count clauses/literals before elimination:
    before_clauses  = poss.size() + negs.size();
    before_literals = 0;
    for (int i = 0; i < poss.size(); i++) before_literals += poss[i].clause->size();
    for (int i = 0; i < negs.size(); i++) before_literals += negs[i].clause->size();
    
    if (poss.size() >= 3 && negs.size() >= 3 && before_literals > 300)  // <<== CUT OFF
        return false;
    
    
    // Count clauses/literals after elimination:
    int after_clauses  = 0;
    int after_literals = 0;
    vec<Lit>  dummy;
    for (int i = 0; i < poss.size(); i++){
        for (int j = 0; j < negs.size(); j++){
            // Merge clauses. If 'y' and '~y' exist, clause will not be created.
            dummy.clear();
            bool ok = merge(*poss[i].clause, *negs[j].clause, Lit(x, false), Lit(x, true), seen_tmp, dummy);
            if (ok){
                after_clauses++;
                if (after_clauses > before_clauses) goto Abort;
                after_literals += dummy.size();
            }
        }
    }
    Abort:;
    
    // Maybe eliminate:
    if (after_clauses  <= before_clauses) {
        vec<ClauseSimp> ps, ns;
        MigrateToPsNs(poss, negs, ps, ns, x);
        for (int i = 0; i < ps.size(); i++) for (int j = 0; j < ns.size(); j++){
            dummy.clear();
            bool ok = merge(*ps[i].clause, *ns[j].clause, Lit(x, false), Lit(x, true), seen_tmp, dummy);
            if (ok){
                solver.addClause(dummy);
                if (solver.clauses.size() + solver.binaryClauses.size() > 0) {
                    Clause* cl =
                    (solver.clauses.size() > 0) ? solver.clauses[0] : solver.binaryClauses[0];
                    
                    solver.clauses.clear(); solver.binaryClauses.clear();
                    if (!isSubsumed(*cl)) {
                        ClauseSimp c = linkInClause(*cl);
                        subsume0(*cl);
                        new_clauses.push(c);
                        solver.ok = (solver.propagate() == NULL);
                    }
                }
                if (!solver.ok) return true;
            }
        }
        DeallocPsNs(ps, ns);
        goto Eliminated;
    }
    
    // Try to remove 'x' from clauses:
    {
        bool    ran = false;
        if (poss.size() < 10) {
            ran = true;
            if (!solver.ok) return true;
        }
        if (negs.size() < 10) {
            ran = true;
            if (!solver.ok) return true;
        }
        if (solver.value(x) != l_Undef) return false;
        if (!ran) return false;
    }
    
    if (!tried_elim) {
        // Count clauses/literals after elimination:
        int after_clauses  = 0;
        int after_literals = 0;
        vec<Lit>  dummy;
        for (int i = 0; i < poss.size(); i++){
            for (int j = 0; j < negs.size(); j++){
                // Merge clauses. If 'y' and '~y' exist, clause will not be created.
                dummy.clear();
                bool ok = merge(*poss[i].clause, *negs[j].clause, Lit(x, false), Lit(x, true), seen_tmp, dummy);
                if (ok){
                    after_clauses++;
                    after_literals += dummy.size();
                }
            }
        }
        
        // Maybe eliminate:
        if (after_clauses  <= before_clauses) {
            vec<ClauseSimp> ps, ns;
            MigrateToPsNs(poss, negs, ps, ns, x);
            for (int i = 0; i < ps.size(); i++) for (int j = 0; j < ns.size(); j++){
                dummy.clear();
                bool ok = merge(*ps[i].clause, *ns[j].clause, Lit(x, false), Lit(x, true), seen_tmp, dummy);
                if (ok){
                    solver.addClause(dummy);
                    if (solver.clauses.size() + solver.binaryClauses.size() > 0) {
                        Clause* cl =
                        (solver.clauses.size() > 0) ? solver.clauses[0] : solver.binaryClauses[0];
                        
                        solver.clauses.clear(); solver.binaryClauses.clear();
                        if (!isSubsumed(*cl)) {
                            ClauseSimp c = linkInClause(*cl);
                            subsume0(*cl);
                            new_clauses.push(c);
                            solver.ok = (solver.propagate() == NULL);
                        }
                    }
                    if (!solver.ok) return true;
                }
            }
            DeallocPsNs(ps, ns);
            goto Eliminated;
        }
    }
    //End try
    
    return false;
    
    Eliminated:
    assert(occur[Lit(x, false).toInt()].size() + occur[Lit(x, true).toInt()].size() == 0);
    var_elimed[x] = 1;
    numElimed++;
    solver.setDecisionVar(x, false);
    return true;
}

// Returns FALSE if clause is always satisfied ('out_clause' should not be used). 'seen' is assumed to be cleared.
bool Subsumer::merge(Clause& ps, Clause& qs, Lit without_p, Lit without_q, vec<char>& seen, vec<Lit>& out_clause)
{
    for (int i = 0; i < ps.size(); i++){
        if (ps[i] != without_p){
            seen[ps[i].toInt()] = 1;
            out_clause.push(ps[i]);
        }
    }
    
    for (int i = 0; i < qs.size(); i++){
        if (qs[i] != without_q){
            if (seen[(~qs[i]).toInt()]){
                for (int i = 0; i < ps.size(); i++)
                    seen[ps[i].toInt()] = 0;
                return false;
            }
            if (!seen[qs[i].toInt()])
                out_clause.push(qs[i]);
        }
    }
    
    for (int i = 0; i < ps.size(); i++)
        seen[ps[i].toInt()] = 0;
    
    return true;
}

struct myComp {
    bool operator () (const pair<int, Var>& x, const pair<int, Var>& y) {
        return x.first < y.first ||
            (!(y.first < x.first) && x.second < y.second);
    }
};
    
// Side-effect: Will untouch all variables.
void Subsumer::orderVarsForElim(vec<Var>& order)
{
    order.clear();
    vec<pair<int, Var> > cost_var;
    for (int i = 0; i < touched_list.size(); i++){
        Var x = touched_list[i];
        touched[x] = 0;
        cost_var.push(std::make_pair( occur[Lit(x, false).toInt()].size() * occur[Lit(x, true).toInt()].size() , x ));
    }
    
    touched_list.clear();
    std::sort(cost_var.getData(), cost_var.getData()+cost_var.size(), myComp());
    
    for (int x = 0; x < cost_var.size(); x++) {
        if (cost_var[x].first != 0)
            order.push(cost_var[x].second);
    }
}

bool Subsumer::isSubsumed(Clause& ps)
{
    for (int j = 0; j < ps.size(); j++){
        vec<ClauseSimp>& cs = occur[ps[j].toInt()];
        
        for (int i = 0; i < cs.size(); i++){
            if (cs[i].clause != &ps && cs[i].clause->size() <= ps.size() && subsetAbst(cs[i].clause->getAbst(), ps.getAbst())){
                if (subset(*cs[i].clause, ps, seen_tmp))
                    return true;
            }
        }
    }
    return false;
}
