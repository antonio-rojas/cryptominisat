/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
**************************************************************************************************/

#include "FailedVarSearcher.h"

#include <iomanip>
#include <utility>
#include <set>
using std::make_pair;
using std::set;

#include "Solver.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "BitArray.h"
#include "VarReplacer.h"

//#define FINDBINARYXOR

FailedVarSearcher::FailedVarSearcher(Solver& _solver):
    solver(_solver)
    , finishedLastTime(true)
    , lastTimeWentUntil(0)
    , numPropsMultiplier(1.0)
    , lastTimeFoundTruths(0)
{
}

void FailedVarSearcher::addFromSolver(vec< XorClause* >& cs)
{
    xorClauseSizes.clear();
    xorClauseSizes.growTo(cs.size());
    occur.resize(solver.nVars());
    for (uint32_t i = 0; i < solver.nVars(); i++) {
        occur[i].clear();
    }
    
    uint32_t i = 0;
    for (XorClause **it = cs.getData(), **end = it + cs.size(); it !=  end; it++, i++) {
        if (it+1 != end)
            __builtin_prefetch(*(it+1), 1, 1);
        
        const XorClause& cl = **it;
        xorClauseSizes[i] = cl.size();
        for (const Lit *l = cl.getData(), *end2 = l + cl.size(); l != end2; l++) {
            occur[l->var()].push_back(&xorClauseSizes[i]);
        }
    }
}

inline void FailedVarSearcher::removeVarFromXors(const Var var)
{
    vector<uint32_t*>& occ = occur[var];
    if (occ.empty()) return;
    
    for (uint32_t **it = &occ[0], **end = it + occ.size(); it != end; it++) {
        (**it)--;
    }
}

inline void FailedVarSearcher::addVarFromXors(const Var var)
{
    vector<uint32_t*>& occ = occur[var];
    if (occ.empty()) return;
    
    for (uint32_t **it = &occ[0], **end = it + occ.size(); it != end; it++) {
        (**it)++;
    }
}

const TwoLongXor FailedVarSearcher::getTwoLongXor(const XorClause& c)
{
    TwoLongXor tmp;
    uint32_t num = 0;
    tmp.inverted = c.xor_clause_inverted();
    
    for(const Lit *l = c.getData(), *end = l + c.size(); l != end; l++) {
        if (solver.assigns[l->var()] == l_Undef) {
            assert(num < 2);
            tmp.var[num] = l->var();
            num++;
        } else {
            tmp.inverted ^= (solver.assigns[l->var()] == l_True);
        }
    }
    
    std::sort(&tmp.var[0], &tmp.var[0]+2);
    assert(num == 2);
    return tmp;
}

const bool FailedVarSearcher::search(uint64_t numProps)
{
    assert(solver.decisionLevel() == 0);
    
    //Saving Solver state
    Heap<Solver::VarOrderLt> backup_order_heap(solver.order_heap);
    vector<bool> backup_polarities = solver.polarity;
    vec<double> backup_activity;
    backup_activity.growTo(solver.activity.size());
    memcpy(backup_activity.getData(), solver.activity.getData(), solver.activity.size()*sizeof(double));
    double backup_var_inc = solver.var_inc;
    
    //General Stats
    double time = cpuTime();
    uint32_t numFailed = 0;
    uint32_t goodBothSame = 0;
    uint32_t from;
    if (finishedLastTime || lastTimeWentUntil >= solver.nVars())
        from = 0;
    else
        from = lastTimeWentUntil;
    uint64_t origProps = solver.propagations;
    
    //If failed var searching is going good, do successively more and more of it
    if (lastTimeFoundTruths > 500 || (double)lastTimeFoundTruths > (double)solver.nVars() * 0.05) std::max(numPropsMultiplier*1.7, 5.0);
    else numPropsMultiplier = 1.0;
    numProps = (uint64_t) ((double)numProps * numPropsMultiplier);
    
    //For failure
    bool failed;
    
    //For BothSame
    BitArray propagated;
    propagated.resize(solver.nVars());
    BitArray propValue;
    propValue.resize(solver.nVars());
    vector<pair<Var, bool> > bothSame;
    
    //For 2-long xor (rule 6 of  Equivalent literal propagation in the DLL procedure by Chu-Min Li)
    set<TwoLongXor> twoLongXors;
    uint32_t toReplaceBefore = solver.varReplacer->getNewToReplaceVars();
    uint32_t lastTrailSize = solver.trail.size();
    bool binXorFind = true;
    if (solver.xorclauses.size() < 5 ||
        solver.xorclauses.size() > 50000 ||
        solver.nVars() > 30000)
        binXorFind = false;
    if (binXorFind) addFromSolver(solver.xorclauses);
    
    finishedLastTime = true;
    lastTimeWentUntil = solver.nVars();
    for (Var var = from; var < solver.nVars(); var++) {
        if (solver.assigns[var] == l_Undef && solver.order_heap.inHeap(var)) {
            if ((int)solver.propagations - (int)origProps >= (int)numProps)  {
                finishedLastTime = false;
                lastTimeWentUntil = var;
                break;
            }
            
            if (binXorFind) {
                if (lastTrailSize < solver.trail.size()) {
                    for (uint32_t i = lastTrailSize; i != solver.trail.size(); i++) {
                        removeVarFromXors(solver.trail[i].var());
                    }
                }
                lastTrailSize = solver.trail.size();
            }
            
            propagated.setZero();
            twoLongXors.clear();
            
            solver.newDecisionLevel();
            solver.uncheckedEnqueue(Lit(var, false));
            failed = (solver.propagate(false) != NULL);
            if (failed) {
                solver.cancelUntil(0);
                numFailed++;
                solver.uncheckedEnqueue(Lit(var, true));
                solver.ok = (solver.propagate(false) == NULL);
                if (!solver.ok) goto end;
                continue;
            } else {
                assert(solver.decisionLevel() > 0);
                for (int c = solver.trail.size()-1; c >= (int)solver.trail_lim[0]; c--) {
                    Var x = solver.trail[c].var();
                    propagated.setBit(x);
                    if (solver.assigns[x].getBool())
                        propValue.setBit(x);
                    else
                        propValue.clearBit(x);
                    
                    if (binXorFind) removeVarFromXors(x);
                }
                
                if (binXorFind) {
                    uint32_t i = 0;
                    for (uint32_t *it = xorClauseSizes.getData(), *end = it + xorClauseSizes.size(); it != end; it++, i++) {
                        if (*it == 2)
                            twoLongXors.insert(getTwoLongXor(*solver.xorclauses[i]));
                    }
                    for (int c = solver.trail.size()-1; c >= (int)solver.trail_lim[0]; c--) {
                        addVarFromXors(solver.trail[c].var());
                    }
                }
                
                solver.cancelUntil(0);
            }
            
            solver.newDecisionLevel();
            solver.uncheckedEnqueue(Lit(var, true));
            failed = (solver.propagate(false) != NULL);
            if (failed) {
                solver.cancelUntil(0);
                numFailed++;
                solver.uncheckedEnqueue(Lit(var, false));
                solver.ok = (solver.propagate(false) == NULL);
                if (!solver.ok) goto end;
                continue;
            } else {
                assert(solver.decisionLevel() > 0);
                for (int c = solver.trail.size()-1; c >= (int)solver.trail_lim[0]; c--) {
                    Var     x  = solver.trail[c].var();
                    if (propagated[x] && propValue[x] == solver.assigns[x].getBool())
                        bothSame.push_back(make_pair(x, !propValue[x]));
                    if (binXorFind) removeVarFromXors(x);
                }
                
                if (binXorFind) {
                    if (twoLongXors.size() > 0) {
                        uint32_t i = 0;
                        for (uint32_t *it = xorClauseSizes.getData(), *end = it + xorClauseSizes.size(); it != end; it++, i++) {
                            if (*it == 2) {
                                TwoLongXor tmp = getTwoLongXor(*solver.xorclauses[i]);
                                if (twoLongXors.find(tmp) != twoLongXors.end()) {
                                    vec<Lit> ps(2);
                                    ps[0] = Lit(tmp.var[0], false);
                                    ps[1] = Lit(tmp.var[1], false);
                                    if (!solver.varReplacer->replace(ps, tmp.inverted, 0))
                                        goto end;
                                }
                            }
                        }
                    }
                    for (int c = solver.trail.size()-1; c >= (int)solver.trail_lim[0]; c--) {
                        addVarFromXors(solver.trail[c].var());
                    }
                }
                
                solver.cancelUntil(0);
            }
            
            for(uint32_t i = 0; i != bothSame.size(); i++) {
                solver.uncheckedEnqueue(Lit(bothSame[i].first, bothSame[i].second));
            }
            goodBothSame += bothSame.size();
            bothSame.clear();
            solver.ok = (solver.propagate(false) == NULL);
            if (!solver.ok) goto end;
        }
    }

end:
    //Restoring Solver state
    //if (solver.verbosity >= 1) {
        std::cout << "c |  Failvars: "<< std::setw(5) << numFailed <<
        "     Bprop vars: " << std::setw(6) << goodBothSame <<
        " Replaced: " << std::setw(3) << (solver.varReplacer->getNewToReplaceVars() - toReplaceBefore) <<
        " Props: " << std::setw(8) << std::setprecision(2) << (int)solver.propagations - (int)origProps  <<
        " Time: " << std::setw(6) << std::fixed << std::setprecision(2) << cpuTime() - time <<
        std::setw(5) << " |" << std::endl;
    //}
    
    if (solver.ok && (numFailed || goodBothSame)) {
        double time = cpuTime();
        solver.clauseCleaner->removeAndCleanAll();
        if (solver.verbosity >= 1 && numFailed + goodBothSame > 100) {
            std::cout << "c |  Cleaning up after failed var search: " << std::setw(8) << std::fixed << std::setprecision(2) << cpuTime() - time << " s "
            <<  std::setw(33) << " | " << std::endl;
        }
    }
    
    lastTimeFoundTruths = goodBothSame + numFailed;
    
    solver.var_inc = backup_var_inc;
    memcpy(solver.activity.getData(), backup_activity.getData(), solver.activity.size()*sizeof(double));
    solver.order_heap = backup_order_heap;
    solver.polarity = backup_polarities;
    solver.order_heap.filter(Solver::VarFilter(solver));
    
    return solver.ok;
}
