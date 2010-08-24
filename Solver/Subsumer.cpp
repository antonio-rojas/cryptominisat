/**************************************************************************************************
Originally From: Solver.C -- (C) Niklas Een, Niklas Sorensson, 2004
Substantially modified by: Mate Soos (2010)
**************************************************************************************************/

#include "Solver.h"
#include "Subsumer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "assert.h"
#include <iomanip>
#include <cmath>
#include <algorithm>
#include "VarReplacer.h"
#include "XorFinder.h"
#include "OnlyNonLearntBins.h"
#include "CompleteDetachReattacher.h"

#ifdef _MSC_VER
#define __builtin_prefetch(a,b,c)
#endif //_MSC_VER

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
    solver(s)
    , totalTime(0.0)
    , numElimed(0)
    , numCalls(1)
{
};

void Subsumer::extendModel(Solver& solver2)
{
    assert(checkElimedUnassigned());
    vec<Lit> tmp;
    typedef map<Var, vector<Clause*> > elimType;
    for (elimType::iterator it = elimedOutVar.begin(), end = elimedOutVar.end(); it != end; it++) {
        #ifndef NDEBUG
        Var var = it->first;
        #ifdef VERBOSE_DEBUG
        std::cout << "Reinserting elimed var: " << var+1 << std::endl;
        #endif
        assert(!solver.decision_var[var]);
        assert(solver.assigns[var] == l_Undef);
        assert(!solver.order_heap.inHeap(var));
        #endif
        
        for (vector<Clause*>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            Clause& c = **it2;
            tmp.clear();
            tmp.growTo(c.size());
            std::copy(c.getData(), c.getDataEnd(), tmp.getData());
            
            #ifdef VERBOSE_DEBUG
            std::cout << "Reinserting Clause: ";
            c.plainPrint();
            #endif
            
            solver2.addClause(tmp);
            assert(solver2.ok);
        }
    }
}

const bool Subsumer::unEliminate(const Var var)
{
    assert(var_elimed[var]);
    vec<Lit> tmp;
    typedef map<Var, vector<Clause*> > elimType;
    elimType::iterator it = elimedOutVar.find(var);

    //it MUST have been decision var, otherwise we would
    //never have removed it
    solver.setDecisionVar(var, true);
    var_elimed[var] = false;
    numElimed--;
    
    //If the variable was removed because of
    //pure literal removal (by blocked clause
    //elimination, there are no clauses to re-insert
    if (it == elimedOutVar.end()) return solver.ok;
    
    FILE* backup_libraryCNFfile = solver.libraryCNFFile;
    solver.libraryCNFFile = NULL;
    for (vector<Clause*>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
        solver.addClause(**it2);
        solver.clauseAllocator.clauseFree(*it2);
    }
    solver.libraryCNFFile = backup_libraryCNFfile;
    elimedOutVar.erase(it);
    
    return solver.ok;
}

void Subsumer::subsume0(Clause& ps)
{
    if (!subsWithBins) ps.subsume0Finished();
    #ifdef VERBOSE_DEBUG
    cout << "subsume0-ing with clause: ";
    ps.plainPrint();
    #endif
    subsume0Happened ret = subsume0Orig(ps, ps.getAbst());
    
    if (ps.learnt()) {
        if (!ret.subsumedNonLearnt) {
            if (ps.activity() > ret.activity)
                ps.setActivity(ret.activity);
            if (ps.oldActivity() < ret.oldActivity)
                ps.setOldActivity(ret.oldActivity);
        } else {
            solver.nbCompensateSubsumer++;
            ps.makeNonLearnt();
        }
    }
}

void Subsumer::subsume0(vec<Lit>& ps, uint32_t abs)
{
    #ifdef VERBOSE_DEBUG
    cout << "subsume0-ing with vec: ";
    printClause(ps);
    #endif
    subsume0Orig(ps, abs);
}

// Will put NULL in 'cs' if clause removed.
template<class T>
Subsumer::subsume0Happened Subsumer::subsume0Orig(const T& ps, uint32_t abs)
{
    subsume0Happened ret;
    ret.subsumedNonLearnt = false;
    ret.activity = std::numeric_limits<uint32_t>::max();
    ret.oldActivity = std::numeric_limits< float >::min();
    
    vec<ClauseSimp> subs;
    findSubsumed(ps, abs, subs);
    for (uint32_t i = 0; i < subs.size(); i++){
        #ifdef VERBOSE_DEBUG
        cout << "-> subsume0 removing:";
        subs[i].clause->plainPrint();
        #endif
        
        Clause* tmp = subs[i].clause;
        if (tmp->learnt()) {
            solver.nbCompensateSubsumer++;
            ret.activity = std::min(ret.activity, tmp->activity());
            ret.oldActivity = std::max(ret.oldActivity, tmp->oldActivity());
        } else {
            ret.subsumedNonLearnt = true;
        }
        unlinkClause(subs[i]);
    }

    return ret;
}

void Subsumer::subsume0BIN(const Lit lit1, const vec<char>& lits)
{
    vec<ClauseSimp> subs;
    vec<ClauseSimp> subs2;
    vec<Lit> subs2Lit;

    vec<ClauseSimp>& cs = occur[lit1.toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 0, 1);
        if (it->clause == NULL) continue;
        Clause& c = *it->clause;
        extraTimeNonExist += c.size()*3;
        bool removed = false;
        for (uint32_t i = 0; i < c.size(); i++) {
            if (lits[c[i].toInt()]) {
                subs.push(*it);
                removed = true;
                break;
            }
        }
        if (removed) continue;

        for (uint32_t i = 0; i < c.size(); i++) {
            if (lits[(~c[i]).toInt()]) {
                subs2.push(*it);
                subs2Lit.push(c[i]);
            }
        }
    }

    for (uint32_t i = 0; i < subs.size(); i++){
        unlinkClause(subs[i]);
    }

    Clause* lastCl = NULL;
    Clause* thisCl = NULL;
    for (uint32_t i = 0; i < subs2.size(); i++) {
        thisCl = subs2[i].clause;
        if (thisCl != lastCl) {
            strenghten(subs2[i], subs2Lit[i], true);
            if (subs2[i].clause == NULL) lastCl = thisCl;
        }
        if (!solver.ok) break;
    }

    #ifdef VERBOSE_DEBUG
    if (!solver.ok) {
        std::cout << "solver.ok is false when returning from subsume0BIN()" << std::endl;
    }
    #endif //VERBOSE_DEBUG
}

void Subsumer::subsume1(Clause& ps)
{
    vec<ClauseSimp>    subs;
    vec<Lit>           subsLits;
    #ifdef VERBOSE_DEBUG
    cout << "subsume1-ing with clause:";
    ps.plainPrint();
    #endif

    findSubsumed1(ps, ps.getAbst(), subs, subsLits);
    ps.unsetStrenghtened();
    if (!subsWithBins) ps.subsume0Finished();
    for (uint32_t j = 0; j < subs.size(); j++) {
        if (subs[j].clause == NULL) continue;
        ClauseSimp c = subs[j];
        if (subsLits[j] == lit_Undef) {
            if (ps.learnt()) {
                if (c.clause->learnt()) {
                    if (c.clause->activity() < ps.activity())
                        ps.setActivity(c.clause->activity());
                    if (c.clause->oldActivity() > ps.oldActivity())
                        ps.setOldActivity(c.clause->oldActivity());
                } else {
                    ps.makeNonLearnt();
                }
            }
            unlinkClause(c);
        } else {
            strenghten(c, subsLits[j]);
            if (!solver.ok) return;
        }
    }
}

void Subsumer::unlinkClause(ClauseSimp c, const Var elim)
{
    Clause& cl = *c.clause;

    for (uint32_t i = 0; i < cl.size(); i++) {
        maybeRemove(occur[cl[i].toInt()], &cl);
        #ifndef TOUCH_LESS
        touch(cl[i]);
        #endif
    }

    // Remove from iterator vectors/sets:
    for (uint32_t i = 0; i < iter_sets.size(); i++) {
        CSet& cs = *iter_sets[i];
        cs.exclude(c);
    }

    // Remove clause from clause touched set:
    cl_touched.exclude(c);

    if (elim != var_Undef) {
        assert(!cl.learnt());
        #ifdef VERBOSE_DEBUG
        std::cout << "Eliminating clause: "; c.clause->plainPrint();
        std::cout << "On variable: " << elim+1 << std::endl;
        #endif //VERBOSE_DEBUG
        elimedOutVar[elim].push_back(c.clause);
    } else {
        clauses_subsumed++;
        solver.clauseAllocator.clauseFree(c.clause);
    }

    clauses[c.index].clause = NULL;
}

const bool Subsumer::cleanClause(Clause& ps)
{
    bool retval = false;

    Lit *i = ps.getData();
    Lit *j = i;
    for (Lit *end = ps.getDataEnd(); i != end; i++) {
        lbool val = solver.value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }
        if (val == l_False) {
            removeW(occur[i->toInt()], &ps);
            #ifndef TOUCH_LESS
            touch(*i);
            #endif
            continue;
        }
        if (val == l_True) {
            *j++ = *i;
            retval = true;
            continue;
        }
        assert(false);
    }
    ps.shrink(i-j);

    return retval;
}

void Subsumer::strenghten(ClauseSimp& c, const Lit toRemoveLit, const bool searchForLit)
{
    #ifdef VERBOSE_DEBUG
    cout << "-> Strenghtening clause :";
    c.clause->plainPrint();
    cout << " with lit: " << (toRemoveLit.sign() ? "-" : "") << toRemoveLit.var()+1 << std::endl;
    #endif

    if (searchForLit && !find(*c.clause, toRemoveLit)) return;
    literals_removed++;
    c.clause->strengthen(toRemoveLit);
    removeW(occur[toRemoveLit.toInt()], c.clause);
    #ifndef TOUCH_LESS
    touch(toRemoveLit);
    #endif
    if (cleanClause(*c.clause)) {
        unlinkClause(c);
        c.clause = NULL;
        return;
    }

    switch (c.clause->size()) {
        case 0:
            #ifdef VERBOSE_DEBUG
            std::cout << "Strenghtened clause to 0-size -> UNSAT"<< std::endl;
            #endif //VERBOSE_DEBUG
            solver.ok = false;
            break;
        case 1: {
            handleSize1Clause((*c.clause)[0]);
            unlinkClause(c);
            c.clause = NULL;
            break;
        }
        default:
            cl_touched.add(c);
    }
}

inline void Subsumer::handleSize1Clause(const Lit lit)
{
    if (solver.value(lit) == l_False) {
        solver.ok = false;
    } else if (solver.value(lit) == l_Undef) {
        solver.uncheckedEnqueue(lit);
        solver.ok = solver.propagate().isNULL();
    } else {
        assert(solver.value(lit) == l_True);
    }
}

void Subsumer::subsume0AndSubsume1()
{
    CSet s0, s1;

    if (cl_touched.size() < clauses.size() / 2) {
        vec<char> ol_seenPos(solver.nVars()*2, 0);
        vec<char> ol_seenNeg(solver.nVars()*2, 0);
        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause == NULL) continue;
            ClauseSimp& c = *it;
            Clause& cl = *it->clause;

            uint32_t smallestPosSize = std::numeric_limits<uint32_t>::max();
            Lit smallestPos = lit_Undef;
            s1.add(c);
            for (uint32_t j = 0; j < cl.size(); j++) {
                if (ol_seenPos[cl[j].toInt()] || smallestPos == lit_Error) {
                    smallestPos = lit_Error;
                    goto next;
                }
                if (occur[cl[j].toInt()].size() < smallestPosSize) {
                    smallestPos = cl[j];
                    smallestPosSize = occur[cl[j].toInt()].size();
                }

                next:
                if (ol_seenNeg[cl[j].toInt()]) continue;
                ol_seenNeg[cl[j].toInt()] = 1;

                vec<ClauseSimp>& n_occs = occur[(~cl[j]).toInt()];
                for (uint32_t k = 0; k < n_occs.size(); k++) s1.add(n_occs[k]);
            }

            if (smallestPos != lit_Undef && smallestPos != lit_Error) {
                ol_seenPos[smallestPos.toInt()] = 1;
                vec<ClauseSimp>& p_occs = occur[smallestPos.toInt()];
                for (uint32_t k = 0; k < p_occs.size(); k++) s0.add(p_occs[k]);
            }
        }
    } else {
        for (uint32_t i = 0; i < clauses.size(); i++) {
            if (clauses[i].clause != NULL) {
                s0.add(clauses[i]);
                s1.add(clauses[i]);
            }
        }
    }
    cl_touched.clear();

    registerIteration(s0);
    registerIteration(s1);

    // Fixed-point for 1-subsumption:
    do {
        for (CSet::iterator it = s0.begin(), end = s0.end(); it != end; ++it) {
            if (it->clause == NULL) continue;
            if (numMaxSubsume0 == 0) break;
            if (it->clause != NULL) {
                subsume0(*it->clause);
                numMaxSubsume0--;
            }
        }
        s0.clear();

        for (CSet::iterator it = s1.begin(), end = s1.end(); it != end; ++it) {
            if (numMaxSubsume1 == 0) break;
            if (it->clause != NULL) {
                subsume1(*it->clause);
                s0.exclude(*it);
                numMaxSubsume1--;
                if (!solver.ok) goto end;
            }
        }
        s1.clear();

        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause != NULL) {
                s1.add(*it);
                s0.add(*it);
            }
        }
        cl_touched.clear();
    } while (s1.size() > 100 || s0.size() > 100);
    assert(cl_touched.size() == 0);

    end:
    unregisterIteration(s1);
    unregisterIteration(s0);
}

ClauseSimp Subsumer::linkInClause(Clause& cl)
{
    ClauseSimp c(&cl, clauseID++);
    clauses.push(c);
    for (uint32_t i = 0; i < cl.size(); i++) {
        occur[cl[i].toInt()].push(c);
        touch(cl[i].var());
    }
    cl_touched.add(c);
    
    return c;
}

void Subsumer::addFromSolver(vec<Clause*>& cs, const bool alsoLearnt, const bool addBinAndAddToCL)
{
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end = i + cs.size(); i !=  end; i++) {
        if (i+1 != end)
            __builtin_prefetch(*(i+1), 1, 1);

        if (!alsoLearnt && (*i)->learnt()) {
            *j++ = *i;
            (*i)->setUnsorted();
            continue;
        }

        if (!addBinAndAddToCL && (*i)->size() == 2) {
            //don't add binary clauses in this case
            *j++ = *i;
            (*i)->setUnsorted();
            continue;
        }

        ClauseSimp c(*i, clauseID++);
        clauses.push(c);
        Clause& cl = *c.clause;
        for (uint32_t i = 0; i < cl.size(); i++) {
            occur[cl[i].toInt()].push(c);
            touch(cl[i].var());
        }
        
        if (addBinAndAddToCL) {
            if (cl.getStrenghtened()) cl_touched.add(c);
        }
    }
    cs.shrink(i-j);
}

void Subsumer::freeMemory()
{
    for (uint32_t i = 0; i < occur.size(); i++) {
        occur[i].clear(true);
    }
}

void Subsumer::addBackToSolver()
{
    #ifdef HYPER_DEBUG2
    uint32_t binaryLearntAdded = 0;
    #endif

    assert(solver.clauses.size() == 0);
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause != NULL) {
            assert(clauses[i].clause->size() > 1);
            if (clauses[i].clause->size() == 2) {
                #ifdef HYPER_DEBUG2
                if (clauses[i].clause->learnt())
                    binaryLearntAdded++;
                #endif
                Clause* c = clauses[i].clause;
                if (!c->wasBin()) {
                    //solver.detachClause(*c);
                    Clause *c2 = solver.clauseAllocator.Clause_new(*c);
                    solver.clauseAllocator.clauseFree(c);
                    //solver.attachClause(*c2);
                    solver.becameBinary++;
                    c = c2;
                }
                solver.binaryClauses.push(c);
            } else {
                if (clauses[i].clause->learnt())
                    solver.learnts.push(clauses[i].clause);
                else
                    solver.clauses.push(clauses[i].clause);
            }
        }
    }
    
    #ifdef HYPER_DEBUG2
    std::cout << "Binary learnt added:" << binaryLearntAdded << std::endl;
    #endif
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
                //solver.detachClause(c);
                solver.clauseAllocator.clauseFree(&c);
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
    std::fill(cannot_eliminate.getData(), cannot_eliminate.getDataEnd(), false);
    for (uint32_t i = 0; i < solver.xorclauses.size(); i++) {
        const XorClause& c = *solver.xorclauses[i];
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }
    
    const vec<Clause*>& tmp = solver.varReplacer->getClauses();
    for (uint32_t i = 0; i < tmp.size(); i++) {
        const Clause& c = *tmp[i];
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }
    
    #ifdef VERBOSE_DEBUG
    uint32_t tmpNum = 0;
    for (uint32_t i = 0; i < cannot_eliminate.size(); i++)
        if (cannot_eliminate[i])
            tmpNum++;
    std::cout << "Cannot eliminate num:" << tmpNum << std::endl;
    #endif
}

const bool Subsumer::subsumeWithBinaries(OnlyNonLearntBins* onlyNonLearntBins)
{
    clearAll();
    clauseID = 0;
    subsWithBins = true;

    //Clearing stats
    clauses_subsumed = 0;
    literals_removed = 0;
    double myTime = cpuTime();
    uint32_t origTrailSize = solver.trail.size();

    clauses.reserve(solver.clauses.size());
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    addFromSolver(solver.clauses, true, false);
    //solver.clauseCleaner->cleanClauses(solver.learnts, ClauseCleaner::learnts);
    //addFromSolver(solver.learnts, true, false);
    CompleteDetachReatacher reattacher(solver);
    reattacher.detachPointerUsingClauses();

    #ifdef DEBUG_BINARIES
    for (uint32_t i = 0; i < clauses.size(); i++) {
        assert(clauses[i].clause->size() != 2);
    }
    #endif //DEBUG_BINARIES

    numMaxSubsume0 = 2000000 * (numCalls);

    for (uint32_t i = 0; i < solver.binaryClauses.size(); i++) {
        if (numMaxSubsume0 > 0) {
            Clause& cl = *solver.binaryClauses[i];
            subsume1(cl);
            if (!solver.ok) return false;
            numMaxSubsume0--;
        }
    }
    subsume0Touched();

    if (solver.verbosity >= 1) {
        std::cout << "c subs with bin: " << std::setw(8) << clauses_subsumed
        << "  lits-rem: " << std::setw(9) << literals_removed
        << "  v-fix: " << std::setw(4) <<solver.trail.size() - origTrailSize
        << "  time: " << std::setprecision(2) << std::setw(5) <<  cpuTime() - myTime << " s"
        << std::endl;
    }
    totalTime += cpuTime() - myTime;
    myTime = cpuTime();

    uint32_t oldTrailSize = solver.trail.size();
    literals_removed = 0;
    clauses_subsumed = 0;
    if (!subsWNonExistBinsFull(onlyNonLearntBins)) return false;
    subsume0Touched();

    #ifdef DEBUG_BINARIES
    for (uint32_t i = 0; i < clauses.size(); i++) {
        assert(clauses[i].clause == NULL || clauses[i].clause->size() != 2);
    }
    #endif //DEBUG_BINARIES

    addBackToSolver();
    reattacher.completelyDetach();
    if (!reattacher.completelyReattach()) return false;
    freeMemory();

    if (solver.verbosity >= 1) {
        std::cout << "c Subs w/ non-existent bins: " << std::setw(6) << clauses_subsumed
        << " l-rem: " << std::setw(6) << literals_removed
        << " v-fix: " << std::setw(5) << solver.trail.size() - oldTrailSize
        << " done: " << std::setw(6) << doneNum
        << " time: " << std::fixed << std::setprecision(2) << std::setw(5) << (cpuTime() - myTime) << " s"
        << std::endl;
    }

    totalTime += cpuTime() - myTime;
    solver.order_heap.filter(Solver::VarFilter(solver));

    return true;
}

void Subsumer::subsume0Touched()
{
    for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
        if (it->clause == NULL) continue;
        Clause& cl = *it->clause;
        subsume0(cl);
    }
    cl_touched.clear();
}

#define MAX_BINARY_PROP 60000000

const bool Subsumer::subsWNonExistBinsFull(OnlyNonLearntBins* onlyNonLearntBins)
{
    uint64_t oldProps = solver.propagations;
    uint64_t maxProp = MAX_BINARY_PROP;
    //if (clauses.size() > 2000000) maxProp /= 2;
    toVisitAll.growTo(solver.nVars()*2, false);
    extraTimeNonExist = 0;

    doneNum = 0;
    uint32_t startFrom = solver.mtrand.randInt(solver.order_heap.size());
    for (uint32_t i = 0; i < solver.order_heap.size(); i++) {
        Var var = solver.order_heap[(i+startFrom)%solver.order_heap.size()];
        if (solver.propagations + extraTimeNonExist - oldProps > maxProp) break;
        if (solver.assigns[var] != l_Undef || !solver.decision_var[var]) continue;
        doneNum++;
        extraTimeNonExist += 5;

        Lit lit(var, true);
        if (onlyNonLearntBins->getWatchSize(lit) == 0) goto next;
        if (!subsWNonExistBins(lit, onlyNonLearntBins)) {
            if (!solver.ok) return false;
            solver.cancelUntil(0);
            solver.uncheckedEnqueue(~lit);
            solver.ok = solver.propagate().isNULL();
            if (!solver.ok) return false;
            continue;
        }
        extraTimeNonExist += 10;
        next:

        //in the meantime it could have got assigned
        if (solver.assigns[var] != l_Undef) continue;
        lit = ~lit;
        if (onlyNonLearntBins->getWatchSize(lit) == 0) continue;
        if (!subsWNonExistBins(lit, onlyNonLearntBins)) {
            if (!solver.ok) return false;
            solver.cancelUntil(0);
            solver.uncheckedEnqueue(~lit);
            solver.ok = solver.propagate().isNULL();
            if (!solver.ok) return false;
            continue;
        }
        extraTimeNonExist += 10;
    }

    return true;
}

const bool Subsumer::subsWNonExistBins(const Lit& lit, OnlyNonLearntBins* onlyNonLearntBins)
{
    #ifdef VERBOSE_DEBUG
    std::cout << "subsWNonExistBins called with lit "; lit.print();
    std::cout << std::endl;
    #endif //VERBOSE_DEBUG
    toVisit.clear();
    solver.newDecisionLevel();
    solver.uncheckedEnqueueLight(lit);
    bool failed = !onlyNonLearntBins->propagate();
    if (failed) return false;

    assert(solver.decisionLevel() > 0);
    for (int c = solver.trail.size()-1; c > (int)solver.trail_lim[0]; c--) {
        Lit x = solver.trail[c];
        toVisit.push(x);
        toVisitAll[x.toInt()] = true;
    }
    solver.cancelUntil(0);

    if (toVisit.size() <= onlyNonLearntBins->getWatchSize(lit)) {
        //This has been performed above, with subsume1Partial of binary clauses:
        //this toVisit.size()<=1, there mustn't have been more than 1 binary
        //clause in the watchlist, so this has been performed above.
    } else {
        subsume0BIN(~lit, toVisitAll);
    }

    for (uint32_t i = 0; i < toVisit.size(); i++)
        toVisitAll[toVisit[i].toInt()] = false;

    return solver.ok;
}

void Subsumer::clearAll()
{
    touched_list.clear();
    touched.clear();
    touched.growTo(solver.nVars(), false);
    for (Var var = 0; var < solver.nVars(); var++) {
        if (solver.decision_var[var] && solver.assigns[var] == l_Undef) touch(var);
        occur[2*var].clear();
        occur[2*var+1].clear();
    }
    clauses.clear();
    cl_touched.clear();
}

const bool Subsumer::simplifyBySubsumption(const bool alsoLearnt)
{
    if (solver.nClauses() > 20000000)  return true;
    
    double myTime = cpuTime();
    uint32_t origTrailSize = solver.trail.size();
    clauses_subsumed = 0;
    literals_removed = 0;
    numblockedClauseRemoved = 0;
    clauseID = 0;
    numVarsElimed = 0;
    blockTime = 0.0;
    clearAll();
    subsWithBins = false;
    
    //if (solver.xorclauses.size() < 30000 && solver.clauses.size() < MAX_CLAUSENUM_XORFIND/10) addAllXorAsNorm();

    if (solver.doReplace && !solver.varReplacer->performReplace(true))
        return false;
    fillCannotEliminate();

    uint32_t expected_size;
    if (!alsoLearnt)
        expected_size = solver.clauses.size() + solver.binaryClauses.size();
    else
        expected_size = solver.clauses.size() + solver.binaryClauses.size() + solver.learnts.size();
    clauses.reserve(expected_size);
    cl_touched.reserve(expected_size);

    //start with smaller clauses first
    //they will be subsumed first, so makes sense!
    solver.clauseCleaner->removeSatisfied(solver.binaryClauses, ClauseCleaner::binaryClauses);
    addFromSolver(solver.binaryClauses, alsoLearnt);
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    addFromSolver(solver.clauses, alsoLearnt);
    if (alsoLearnt) {
        solver.clauseCleaner->cleanClauses(solver.learnts, ClauseCleaner::learnts);
        addFromSolver(solver.learnts, alsoLearnt);
    }
    //It is IMPERATIVE to add binaryClauses last. The non-binary clauses can
    //move to binaryClauses during cleaning!!!!
    addFromSolver(solver.binaryClauses, alsoLearnt);
    CompleteDetachReatacher reattacher(solver);
    reattacher.detachPointerUsingClauses();

    setLimits(alsoLearnt);

    //For debugging
    //numMaxBlockToVisit = std::numeric_limits<int64_t>::max();
    //numMaxElim = std::numeric_limits<uint32_t>::max();
    //numMaxSubsume0 = std::numeric_limits<uint32_t>::max();
    //numMaxSubsume1 = std::numeric_limits<uint32_t>::max();
    //numMaxBlockVars = std::numeric_limits<uint32_t>::max();
    
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  num clauses:" << clauses.size() << std::endl;
    std::cout << "c  time to link in:" << cpuTime()-myTime << std::endl;
    #endif
    
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (numMaxSubsume0 == 0) break;
        if (clauses[i].clause != NULL && (!clauses[i].clause->subsume0IsFinished() || clauses[i].clause->learnt())) {
            subsume0(*clauses[i].clause);
            numMaxSubsume0--;
        }
    }

    //Because of touched, we will go through this anyway
    //--> s0 will have the important clauses from here in it
    //but for performance reasons, it's probably best to do it anyway
    if (alsoLearnt) {
        for (uint32_t i = 0; i < clauses.size(); i++) {
            if (numMaxSubsume0 == 0) break;
            if (clauses[i].clause != NULL && !clauses[i].clause->learnt()) {
                subsume0(*clauses[i].clause);
                numMaxSubsume0--;
            }
        }
    }

    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  time until pre-subsume0 clauses and subsume1 2-learnts:" << cpuTime()-myTime << std::endl;
    #endif
    
    if (!solver.ok) return false;
    #ifdef VERBOSE_DEBUG
    std::cout << "c   pre-subsumed:" << clauses_subsumed << std::endl;
    std::cout << "c   cl_touched:" << cl_touched.size() << std::endl;
    std::cout << "c   clauses:" << clauses.size() << std::endl;
    #endif
    
    if (clauses.size() > 10000000 ||
        (numMaxSubsume1 == 0 && numMaxElim == 0 && numMaxBlockVars == 0))
        goto endSimplifyBySubsumption;

    if (solver.doBlockedClause && numCalls % 3 == 1) blockedClauseRemoval();
    do {
        #ifdef BIT_MORE_VERBOSITY
        std::cout << "c time before the start of subsume0AndSubsume1(): " << cpuTime() - myTime << std::endl;
        #endif
        subsume0AndSubsume1();
        if (!solver.ok) return false;

        #ifdef BIT_MORE_VERBOSITY
        std::cout << "c time until the end of subsume0AndSubsume1(): " << cpuTime() - myTime << std::endl;
        #endif

        if (!solver.doVarElim) break;

        #ifdef BIT_MORE_VERBOSITY
        printf("c VARIABLE ELIMINIATION\n");
        std::cout << "c  toucheds list size:" << touched_list.size() << std::endl;
        #endif
        vec<Var> init_order;
        orderVarsForElim(init_order);   // (will untouch all variables)

        for (bool first = true; numMaxElim > 0; first = false) {
            uint32_t vars_elimed = 0;
            vec<Var> order;

            if (first) {
                //init_order.copyTo(order);
                for (uint32_t i = 0; i < init_order.size(); i++) {
                    const Var var = init_order[i];
                    if (!cannot_eliminate[var] && solver.decision_var[var])
                        order.push(var);
                }
            } else {
                for (uint32_t i = 0; i < touched_list.size(); i++) {
                    const Var var = touched_list[i];
                    if (!cannot_eliminate[var] && solver.decision_var[var])
                        order.push(var);
                    touched[var] = false;
                }
                touched_list.clear();
            }
            #ifdef VERBOSE_DEBUG
            std::cout << "Order size:" << order.size() << std::endl;
            #endif

            for (uint32_t i = 0; i < order.size() && numMaxElim > 0; i++, numMaxElim--) {
                if (maybeEliminate(order[i])) {
                    if (!solver.ok) return false;
                    vars_elimed++;
                }
            }
            if (vars_elimed == 0) break;

            numVarsElimed += vars_elimed;
            #ifdef BIT_MORE_VERBOSITY
            printf("c  #var-elim: %d\n", vars_elimed);
            std::cout << "c time until the end of varelim: " << cpuTime() - myTime << std::endl;
            #endif
        }
    } while (cl_touched.size() > 100);
    endSimplifyBySubsumption:

    if (!solver.ok) return false;

    assert(verifyIntegrity());

    removeWrong(solver.learnts);
    removeWrong(solver.binaryClauses);
    removeAssignedVarsFromEliminated();

    solver.order_heap.filter(Solver::VarFilter(solver));

    addBackToSolver();
    reattacher.completelyDetach();
    if (!reattacher.completelyReattach()) return false;

    freeMemory();

    if (solver.verbosity >= 1) {
        std::cout << "c lits-rem: " << std::setw(9) << literals_removed
        << "  cl-subs: " << std::setw(8) << clauses_subsumed
        << "  v-elim: " << std::setw(6) << numVarsElimed
        << "  v-fix: " << std::setw(4) <<solver.trail.size() - origTrailSize
        << "  time: " << std::setprecision(2) << std::setw(5) << (cpuTime() - myTime) << " s"
        //<< " blkClRem: " << std::setw(5) << numblockedClauseRemoved
        << std::endl;
        
        if (numblockedClauseRemoved > 0 || blockTime > 0.0) {
            std::cout 
            << "c Blocked clauses removed: " << std::setw(8) << numblockedClauseRemoved
            << "    Time: " << std::fixed << std::setprecision(2) << std::setw(4) << blockTime << " s" 
            << std::endl;
        }
    }
    totalTime += cpuTime() - myTime;

    solver.testAllClauseAttach();
    return true;
}

void Subsumer::setLimits(const bool alsoLearnt)
{
    if (clauses.size() > 3500000) {
        numMaxSubsume0 = 900000 * (1+numCalls/2);
        numMaxElim = (uint32_t)((double)solver.order_heap.size() / 5.0 * (0.8+(double)(numCalls)/4.0));
        numMaxSubsume1 = 100000 * (1+numCalls/2);
        numMaxBlockToVisit = (int64_t)(30000.0 * (0.8+(double)(numCalls)/3.0));
    }
    if (clauses.size() <= 3500000 && clauses.size() > 1500000) {
        numMaxSubsume0 = 2000000 * (1+numCalls/2);
        numMaxElim = (uint32_t)((double)solver.order_heap.size() / 2.0 * (0.8+(double)(numCalls)/4.0));
        numMaxSubsume1 = 300000 * (1+numCalls/2);
        numMaxBlockToVisit = (int64_t)(50000.0 * (0.8+(double)(numCalls)/3.0));
    }
    if (clauses.size() <= 1500000) {
        numMaxSubsume0 = 4000000 * (1+numCalls/2);
        numMaxElim = (uint32_t)((double)solver.order_heap.size() / 2.0 * (0.8+(double)(numCalls)/2.0));
        numMaxSubsume1 = 400000 * (1+numCalls/2);
        numMaxBlockToVisit = (int64_t)(80000.0 * (0.8+(double)(numCalls)/3.0));
    }
    if (solver.order_heap.size() > 200000)
        numMaxBlockVars = (uint32_t)((double)solver.order_heap.size() / 3.5 * (0.8+(double)(numCalls)/4.0));
    else
        numMaxBlockVars = (uint32_t)((double)solver.order_heap.size() / 1.5 * (0.8+(double)(numCalls)/4.0));

    if (!solver.doSubsume1 || numCalls == 1)
        numMaxSubsume1 = 0;
    if (alsoLearnt) {
        numMaxElim = 0;
        numMaxSubsume1 = std::min(numMaxSubsume1, (uint32_t)10000);
        numMaxBlockVars = 0;
        numMaxBlockToVisit = 0;
    } else {
        numCalls++;
    }
}

void Subsumer::removeAssignedVarsFromEliminated()
{
    for (Var var = 0; var < var_elimed.size(); var++) {
        if (var_elimed[var] && solver.assigns[var] != l_Undef) {
            var_elimed[var] = false;
            solver.setDecisionVar(var, true);
            numElimed--;
            map<Var, vector<Clause*> >::iterator it = elimedOutVar.find(var);
            if (it != elimedOutVar.end()) {
                //TODO memory loss here
                elimedOutVar.erase(it);
            }
        }
    }
}

template<class T>
void Subsumer::findSubsumed(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed: ";
    printClause(ps);
    #endif

    for (uint32_t i = 0; i != ps.size(); i++)
        seen_tmp[ps[i].toInt()] = 1;
    
    uint32_t min_i = 0;
    for (uint32_t i = 1; i < ps.size(); i++){
        if (occur[ps[i].toInt()].size() < occur[ps[min_i].toInt()].size())
            min_i = i;
    }
    
    vec<ClauseSimp>& cs = occur[ps[min_i].toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);
        
        if (it->clause != (Clause*)&ps
            && subsetAbst(abs, it->clause->getAbst())
            && ps.size() <= it->clause->size()
            && subset(ps.size(), *it->clause)) {
            out_subsumed.push(*it);
            #ifdef VERBOSE_DEBUG
            cout << "subsumed: ";
            it->clause->plainPrint();
            #endif
        }
    }

    for (uint32_t i = 0; i != ps.size(); i++)
        seen_tmp[ps[i].toInt()] = 0;
}

template<class T>
void Subsumer::findSubsumed1(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed, vec<Lit>& out_lits)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed1: ";
    printClause(ps);
    #endif

    Var minVar = var_Undef;
    uint32_t bestSize = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < ps.size(); i++){
        uint32_t newSize = occur[ps[i].toInt()].size()+ occur[(~ps[i]).toInt()].size();
        if (newSize < bestSize) {
            minVar = ps[i].var();
            bestSize = newSize;
        }
    }
    assert(minVar != var_Undef);

    fillSubs(ps, abs, out_subsumed, out_lits, Lit(minVar, true));
    fillSubs(ps, abs, out_subsumed, out_lits, Lit(minVar, false));
}

template<class T>
void inline Subsumer::fillSubs(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed, vec<Lit>& out_lits, const Lit lit)
{
    Lit litSub;
    vec<ClauseSimp>& cs = occur[lit.toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++) {
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);

        if (it->clause != (Clause*)&ps
            && subsetAbst(abs, it->clause->getAbst())
            && ps.size() <= it->clause->size()) {
            litSub = subset1(ps, *it->clause);
            if (litSub != lit_Error) {
                out_subsumed.push(*it);
                out_lits.push(litSub);
                #ifdef VERBOSE_DEBUG
                if (litSub == lit_Undef) cout << "subsume0-d: ";
                else cout << "subsume1-ed (lit: " << (litSub.sign() ? "-" : "") << litSub.var()+1 << "): ";
                it->clause->plainPrint();
                #endif
            }
        }
    }
}

void inline Subsumer::MigrateToPsNs(vec<ClauseSimp>& poss, vec<ClauseSimp>& negs, vec<ClauseSimp>& ps, vec<ClauseSimp>& ns, const Var x)
{
    poss.moveTo(ps);
    negs.moveTo(ns);
    
    for (uint32_t i = 0; i < ps.size(); i++)
        unlinkClause(ps[i], x);
    for (uint32_t i = 0; i < ns.size(); i++)
        unlinkClause(ns[i], x);
}

// Returns TRUE if variable was eliminated.
bool Subsumer::maybeEliminate(const Var x)
{
    assert(!var_elimed[x]);
    assert(!cannot_eliminate[x]);
    assert(solver.decision_var[x]);
    if (solver.value(x) != l_Undef) return false;
    if (occur[Lit(x, false).toInt()].size() == 0 && occur[Lit(x, true).toInt()].size() == 0)
        return false;
    
    vec<ClauseSimp>&   poss = occur[Lit(x, false).toInt()];
    vec<ClauseSimp>&   negs = occur[Lit(x, true).toInt()];
    
    // Heuristic CUT OFF:
    if (poss.size() >= 10 && negs.size() >= 10)
        return false;
    
    // Count clauses/literals before elimination:
    int before_clauses  = poss.size() + negs.size();
    uint32_t before_literals = 0;
    for (uint32_t i = 0; i < poss.size(); i++) before_literals += poss[i].clause->size();
    for (uint32_t i = 0; i < negs.size(); i++) before_literals += negs[i].clause->size();
    
    // Heuristic CUT OFF2:
    if ((poss.size() >= 3 && negs.size() >= 3 && before_literals > 300)
        && clauses.size() > 1500000)
        return false;
    if ((poss.size() >= 5 && negs.size() >= 5 && before_literals > 400)
        && clauses.size() <= 1500000 && clauses.size() > 200000)
        return false;
    if ((poss.size() >= 8 && negs.size() >= 8 && before_literals > 700)
        && clauses.size() <= 200000)
        return false;
    
    // Count clauses/literals after elimination:
    int after_clauses  = 0;
    vec<Lit>  dummy;
    for (uint32_t i = 0; i < poss.size(); i++) for (uint32_t j = 0; j < negs.size(); j++){
        // Merge clauses. If 'y' and '~y' exist, clause will not be created.
        dummy.clear();
        bool ok = merge(*poss[i].clause, *negs[j].clause, Lit(x, false), Lit(x, true), dummy);
        if (ok){
            after_clauses++;
            if (after_clauses > before_clauses) goto Abort;
        }
    }
    Abort:;

    //Eliminate:
    if (after_clauses  <= before_clauses) {
        vec<ClauseSimp> ps, ns;
        MigrateToPsNs(poss, negs, ps, ns, x);
        for (uint32_t i = 0; i < ps.size(); i++) for (uint32_t j = 0; j < ns.size(); j++){
            dummy.clear();
            bool ok = merge(*ps[i].clause, *ns[j].clause, Lit(x, false), Lit(x, true), dummy);
            if (ok) {
                uint32_t group_num = 0;
                #ifdef STATS_NEEDED
                group_num = solver.learnt_clause_group++;
                if (solver.dynamic_behaviour_analysis) {
                    string name = solver.logger.get_group_name(ps[i].clause->getGroup()) + " " + solver.logger.get_group_name(ns[j].clause->getGroup());
                    solver.logger.set_group_name(group_num, name);
                }
                #endif
                switch (dummy.size()) {
                    case 0:
                        solver.ok = false;
                        break;
                    case 1: {
                        handleSize1Clause(dummy[0]);
                        break;
                    }
                    default: {
                        Clause* cl = solver.clauseAllocator.Clause_new(dummy, group_num);
                        ClauseSimp c = linkInClause(*cl);
                        subsume1(*c.clause);
                    }
                }
                if (!solver.ok) return true;
            }
        }
        goto Eliminated;
    }
    
    return false;
    
    Eliminated:
    assert(occur[Lit(x, false).toInt()].size() + occur[Lit(x, true).toInt()].size() == 0);
    var_elimed[x] = true;
    numElimed++;
    solver.setDecisionVar(x, false);
    return true;
}

// Returns FALSE if clause is always satisfied ('out_clause' should not be used). 'seen' is assumed to be cleared.
bool Subsumer::merge(const Clause& ps, const Clause& qs, const Lit without_p, const Lit without_q, vec<Lit>& out_clause)
{
    for (uint32_t i = 0; i < ps.size(); i++){
        if (ps[i] != without_p){
            seen_tmp[ps[i].toInt()] = 1;
            out_clause.push(ps[i]);
        }
    }
    
    for (uint32_t i = 0; i < qs.size(); i++){
        if (qs[i] != without_q){
            if (seen_tmp[(~qs[i]).toInt()]){
                for (uint32_t i = 0; i < ps.size(); i++)
                    seen_tmp[ps[i].toInt()] = 0;
                return false;
            }
            if (!seen_tmp[qs[i].toInt()])
                out_clause.push(qs[i]);
        }
    }
    
    for (uint32_t i = 0; i < ps.size(); i++)
        seen_tmp[ps[i].toInt()] = 0;
    
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
    for (uint32_t i = 0; i < touched_list.size(); i++){
        Var x = touched_list[i];
        touched[x] = 0;
        cost_var.push(std::make_pair( occur[Lit(x, false).toInt()].size() * occur[Lit(x, true).toInt()].size() , x ));
    }
    
    touched_list.clear();
    std::sort(cost_var.getData(), cost_var.getData()+cost_var.size(), myComp());
    
    for (uint32_t x = 0; x < cost_var.size(); x++) {
        if (cost_var[x].first != 0)
            order.push(cost_var[x].second);
    }
}

const bool Subsumer::verifyIntegrity()
{
    vector<uint32_t> occurNum(solver.nVars()*2, 0);

    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause == NULL) continue;
        Clause& c = *clauses[i].clause;
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            occurNum[c[i2].toInt()]++;
    }

    for (uint32_t i = 0; i < occurNum.size(); i++) {
        #ifdef VERBOSE_DEBUG
        std::cout << "occurNum[i]:" << occurNum[i]
        << " occur[i]:" << occur[i].size()
        << "  --- i:" << i << std::endl;
        #endif //VERBOSE_DEBUG

        if (occurNum[i] != occur[i].size()) return false;
    }

    return true;
}

const bool Subsumer::allTautology(const vec<Lit>& ps, const Lit lit)
{
    #ifdef VERBOSE_DEBUG
    cout << "allTautology: ";
    for (uint32_t i = 0; i < ps.size(); i++) {
        if (ps[i].sign()) printf("-");
        printf("%d ", ps[i].var() + 1);
    }
    printf("0\n");
    #endif
    
    vec<ClauseSimp>& cs = occur[lit.toInt()];
    if (cs.size() == 0) return true;
    
    for (const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        seen_tmp[l->toInt()] = true;
    }
    
    bool allIsTautology = true;
    for (ClauseSimp *it = cs.getData(), *end = cs.getDataEnd(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);
        
        Clause& c = *it->clause;
        for (Lit *l = c.getData(), *end2 = l + c.size(); l != end2; l++) {
            if (*l != lit && seen_tmp[(~(*l)).toInt()]) {
                goto next;
            }
        }
        allIsTautology = false;
        break;
        
        next:;
    }
    
    for (const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        seen_tmp[l->toInt()] = false;
    }
    
    return allIsTautology;
}

void Subsumer::blockedClauseRemoval()
{
    if (numMaxBlockToVisit < 0) return;
    if (solver.order_heap.size() < 1) return;
    double myTime = cpuTime();
    vec<ClauseSimp> toRemove;
    
    touchedBlockedVars = priority_queue<VarOcc, vector<VarOcc>, MyComp>();
    touchedBlockedVarsBool.clear();
    touchedBlockedVarsBool.growTo(solver.nVars(), false);
    for (uint32_t i =  0; i < solver.order_heap.size() && i < numMaxBlockVars; i++) {
        if (solver.order_heap.size() < 1) break;
        touchBlockedVar(solver.order_heap[solver.mtrand.randInt(solver.order_heap.size()-1)]);
    }
    
    while (touchedBlockedVars.size() > 100  && numMaxBlockToVisit > 0) {
        VarOcc vo = touchedBlockedVars.top();
        touchedBlockedVars.pop();
        
        if (solver.assigns[vo.var] != l_Undef || !solver.decision_var[vo.var] || cannot_eliminate[vo.var])
            continue;
        touchedBlockedVarsBool[vo.var] = false;
        Lit lit = Lit(vo.var, false);
        Lit negLit = Lit(vo.var, true);
        
        numMaxBlockToVisit -= (int64_t)occur[lit.toInt()].size();
        numMaxBlockToVisit -= (int64_t)occur[negLit.toInt()].size();
        //if (!tryOneSetting(lit, negLit)) {
            tryOneSetting(negLit, lit);
       // }
    }
    blockTime += cpuTime() - myTime;
    
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  Total fime for block until now: " << blockTime << std::endl;
    #endif
}

const bool Subsumer::tryOneSetting(const Lit lit, const Lit negLit)
{
    uint32_t toRemove = 0;
    bool returnVal = false;
    vec<Lit> cl;
    
    for(ClauseSimp *it = occur[lit.toInt()].getData(), *end = occur[lit.toInt()].getDataEnd(); it != end; it++) {
        cl.clear();
        cl.growTo(it->clause->size()-1);
        for (uint32_t i = 0, i2 = 0; i < it->clause->size(); i++) {
            if ((*it->clause)[i] != lit) {
                cl[i2] = (*it->clause)[i];
                i2++;
            }
        }
        
        if (allTautology(cl, negLit)) {
            toRemove++;
        } else {
            break;
        }
    }
    
    if (toRemove == occur[lit.toInt()].size()) {
        var_elimed[lit.var()] = true;
        solver.setDecisionVar(lit.var(), false);
        vec<ClauseSimp> toRemove(occur[lit.toInt()]);
        for (ClauseSimp *it = toRemove.getData(), *end = toRemove.getDataEnd(); it != end; it++) {
            #ifdef VERBOSE_DEBUG
            std::cout << "Next varelim because of block clause elim" << std::endl;
            #endif //VERBOSE_DEBUG
            unlinkClause(*it, lit.var());
            numblockedClauseRemoved++;
        }
        
        vec<ClauseSimp> toRemove2(occur[negLit.toInt()]);
        for (ClauseSimp *it = toRemove2.getData(), *end = toRemove2.getDataEnd(); it != end; it++) {
            #ifdef VERBOSE_DEBUG
            std::cout << "Next varelim because of block clause elim" << std::endl;
            #endif //VERBOSE_DEBUG
            unlinkClause(*it, lit.var());
            numblockedClauseRemoved++;
        }
        returnVal = true;
    }
    
    return returnVal;
}

const bool Subsumer::checkElimedUnassigned() const
{
    for (uint32_t i = 0; i < var_elimed.size(); i++) {
        if (var_elimed[i]) {
            assert(solver.assigns[i] == l_Undef);
            if (solver.assigns[i] != l_Undef) return false;
        }
    }

    return true;
}
