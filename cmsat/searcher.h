/*
 * CryptoMiniSat
 *
 * Copyright (c) 2009-2011, Mate Soos and collaborators. All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 3.0 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
*/

#ifndef __SEARCHER_H__
#define __SEARCHER_H__

#include "propengine.h"
#include "solvertypes.h"
#include "boost/multi_array.hpp"
#include "time_mem.h"
#include "avgcalc.h"
class Solver;
class SQLStats;

using std::string;
using std::cout;
using std::endl;

struct VariableVariance
{
    double avgDecLevelVarLT;
    double avgTrailLevelVarLT;
    double avgDecLevelVar;
    double avgTrailLevelVar;
};

class Searcher : public PropEngine
{
    public:
        Searcher(const SolverConf& _conf, Solver* solver);
        ~Searcher();

        //History
        struct Hist {
            //About the search
            AvgCalc<uint32_t>   branchDepthHist;     ///< Avg branch depth in current restart
            AvgCalc<uint32_t>   branchDepthHistLT;

            bqueue<uint32_t>    branchDepthDeltaHist;
            AvgCalc<uint32_t>   branchDepthDeltaHistLT;

            AvgCalc<uint32_t>   trailDepthHist;
            AvgCalc<uint32_t>   trailDepthHistLT;

            AvgCalc<uint32_t>   trailDepthDeltaHist;
            AvgCalc<uint32_t>   trailDepthDeltaHistLT;

            AvgCalc<bool>       conflictAfterConflict;
            AvgCalc<bool>       conflictAfterConflictLT;

            //About the confl generated
            bqueue<uint32_t>    glueHist;            ///< Set of last decision levels in (glue of) conflict clauses
            AvgCalc<uint32_t>   glueHistLT;

            bqueue<uint32_t>    conflSizeHist;       ///< Conflict size history
            AvgCalc<uint32_t>   conflSizeHistLT;

            AvgCalc<uint32_t>   numResolutionsHist;  ///< Number of resolutions during conflict analysis
            AvgCalc<uint32_t>   numResolutionsHistLT;

            //lits, vars
            AvgCalc<double, double>  agilityHist;
            AvgCalc<double, double>  agilityHistLT;

            AvgCalc<size_t>     watchListSizeTraversed;
            AvgCalc<size_t>     watchListSizeTraversedLT;

            AvgCalc<bool>       litPropagatedSomething;
            AvgCalc<bool>       litPropagatedSomethingLT;

            void clear()
            {
                //About the search
                branchDepthHistLT.addData(branchDepthHist);
                branchDepthHist.clear();

                branchDepthDeltaHistLT.addData(branchDepthDeltaHist.getLongtTerm());
                branchDepthDeltaHist.clear();

                trailDepthHistLT.addData(trailDepthHist);
                trailDepthHist.clear();

                trailDepthDeltaHistLT.addData(trailDepthDeltaHist);
                trailDepthDeltaHist.clear();

                conflictAfterConflictLT.addData(conflictAfterConflict);
                conflictAfterConflict.clear();

                //conflict generated
                glueHistLT.addData(glueHist.getLongtTerm());
                glueHist.clear();

                conflSizeHistLT.addData(conflSizeHist.getLongtTerm());
                conflSizeHist.clear();

                numResolutionsHistLT.addData(numResolutionsHist);
                numResolutionsHist.clear();

                //lits, vars
                agilityHistLT.addData(agilityHist);
                agilityHist.clear();

                watchListSizeTraversedLT.addData(watchListSizeTraversed);
                watchListSizeTraversed.clear();

                litPropagatedSomethingLT.addData(litPropagatedSomething);
                litPropagatedSomething.clear();
            }

            void reset(const size_t shortTermHistorySize)
            {
                //About the search tree
                branchDepthHist.clear();
                branchDepthHistLT.clear();

                branchDepthDeltaHist.clearAndResize(shortTermHistorySize);
                branchDepthDeltaHistLT.clear();

                trailDepthHist.clear();
                trailDepthHistLT.clear();

                trailDepthDeltaHist.clear();
                trailDepthDeltaHistLT.clear();

                conflictAfterConflict.clear();
                conflictAfterConflictLT.clear();

                //About the confl generated
                glueHist.clearAndResize(shortTermHistorySize);
                glueHistLT.clear();

                conflSizeHist.clearAndResize(shortTermHistorySize);
                conflSizeHistLT.clear();

                numResolutionsHist.clear();
                numResolutionsHistLT.clear();

                //Lits, vars
                agilityHist.clear();
                agilityHistLT.clear();

                watchListSizeTraversed.clear();
                watchListSizeTraversedLT.clear();

                litPropagatedSomething.clear();
                litPropagatedSomethingLT.clear();
            }

            void print() const
            {
                cout
                << " glue"
                << " " << std::right << glueHist.getLongtTerm().avgPrint(1, 5)
                << "/" << std::left << glueHistLT.avgPrint(1, 5)

                << " agil"
                << " " << std::right << agilityHist.avgPrint(3, 5)
                << "/" << std::left<< agilityHistLT.avgPrint(3, 5)

                << " confllen"
                << " " << std::right << conflSizeHist.getLongtTerm().avgPrint(1, 5)
                << "/" << std::left << conflSizeHistLT.avgPrint(1, 5)

                << " branchd"
                << " " << std::right << branchDepthHist.avgPrint(1, 5)
                << "/" << std::left  << branchDepthHistLT.avgPrint(1, 5)
                << " branchdd"

                << " " << std::right << branchDepthDeltaHist.getLongtTerm().avgPrint(1, 4)
                << "/" << std::left << branchDepthDeltaHistLT.avgPrint(1, 4)

                << " traild"
                << " " << std::right << trailDepthHist.avgPrint(0, 7)
                << "/" << std::left << trailDepthHistLT.avgPrint(0, 7)

                << " traildd"
                << " " << std::right << trailDepthDeltaHist.avgPrint(0, 5)
                << "/" << std::left << trailDepthDeltaHistLT.avgPrint(0, 5)
                ;

                cout << std::right;
            }
        };

        //////////////////////////////
        // Problem specification:
        Var newVar(bool dvar = true); // Add a new variable that can be decided on or not

        ///////////////////////////////
        // Solving:
        ///Search for a model that respects a given set of assumptions.
        lbool solve(
            const vector<Lit>& assumps
            , const uint64_t maxConfls = std::numeric_limits<uint64_t>::max()
        );

        ///Search without assumptions.
        lbool solve(
            const uint64_t maxConfls = std::numeric_limits<uint64_t>::max()
        );
        vector<lbool> solution;     ///<Filled only if solve() returned l_True
        vector<Lit>   conflict;     ///<If problem is unsatisfiable (possibly under assumptions), this vector represent the final conflict clause expressed in the assumptions.

        ///////////////////////////////
        // Stats
        void     printRestartHeader() const;
        void     printRestartStats() const;
        void     printBaseStats() const;
        void     printClauseStats() const;
        uint64_t sumConflicts() const;
        uint64_t sumRestarts() const;
        const Hist& getHistory() const;

        void     setNeedToInterrupt();
        uint32_t getSavedActivity(Var var) const;
        uint32_t getVarInc() const;

        struct Stats
        {
            Stats() :
                // Stats
                numRestarts(0)

                //Decisions
                , decisions(0)
                , decisionsAssump(0)
                , decisionsRand(0)
                , decisionFlippedPolar(0)

                //Conflict generation
                , litsLearntNonMin(0)
                , litsLearntRecMin(0)
                , litsLearntFinal(0)
                , OTFShrinkAttempted(0)
                , OTFShrinkedClause(0)

                //Learnt stats
                , learntUnits(0)
                , learntBins(0)
                , learntTris(0)
                , learntLongs(0)
                , otfSubsumed(0)
                , otfSubsumedLearnt(0)
                , otfSubsumedLitsGained(0)

                //Hyper-bin & transitive reduction
                , advancedPropCalled(0)
                , hyperBinAdded(0)
                , transRedRemoved(0)

                //Time
                , cpu_time(0)

            {};

            void clear()
            {
                Stats stats;
                *this = stats;
            }

            Stats& operator+=(const Stats& other)
            {
                numRestarts += other.numRestarts;

                //Decisions
                decisions += other.decisions;
                decisionsAssump += other.decisionsAssump;
                decisionsRand += other.decisionsRand;
                decisionFlippedPolar += other.decisionFlippedPolar;

                //Conflict minimisation stats
                litsLearntNonMin += other.litsLearntNonMin;
                litsLearntRecMin += other.litsLearntRecMin;
                litsLearntFinal += other.litsLearntFinal;
                OTFShrinkAttempted  += other.OTFShrinkAttempted;
                OTFShrinkedClause += other.OTFShrinkedClause;

                //Learnt stats
                learntUnits += other.learntUnits;
                learntBins += other.learntBins;
                learntTris += other.learntTris;
                learntLongs += other.learntLongs;
                otfSubsumed += other.otfSubsumed;
                otfSubsumedLearnt += other.otfSubsumedLearnt;
                otfSubsumedLitsGained += other.otfSubsumedLitsGained;

                //Hyper-bin & transitive reduction
                advancedPropCalled += other.advancedPropCalled;
                hyperBinAdded += other.hyperBinAdded;
                transRedRemoved += other.transRedRemoved;

                //Stat structs
                conflStats += other.conflStats;

                //Time
                cpu_time += other.cpu_time;

                return *this;
            }

            Stats& operator-=(const Stats& other)
            {
                numRestarts -= other.numRestarts;

                //Decisions
                decisions -= other.decisions;
                decisionsAssump -= other.decisionsAssump;
                decisionsRand -= other.decisionsRand;
                decisionFlippedPolar -= other.decisionFlippedPolar;

                //Conflict minimisation stats
                litsLearntNonMin -= other.litsLearntNonMin;
                litsLearntRecMin -= other.litsLearntRecMin;
                litsLearntFinal -= other.litsLearntFinal;
                OTFShrinkAttempted  -= other.OTFShrinkAttempted;
                OTFShrinkedClause -= other.OTFShrinkedClause;

                //Learnt stats
                learntUnits -= other.learntUnits;
                learntBins -= other.learntBins;
                learntTris -= other.learntTris;
                learntLongs -= other.learntLongs;
                otfSubsumed -= other.otfSubsumed;
                otfSubsumedLearnt -= other.otfSubsumedLearnt;
                otfSubsumedLitsGained -= other.otfSubsumedLitsGained;

                //Hyper-bin & transitive reduction
                advancedPropCalled -= other.advancedPropCalled;
                hyperBinAdded -= other.hyperBinAdded;
                transRedRemoved -= other.transRedRemoved;

                //Stat structs
                conflStats -= other.conflStats;

                //Time
                cpu_time -= other.cpu_time;

                return *this;
            }

            Stats operator-(const Stats& other) const
            {
                Stats result = *this;
                result -= other;
                return result;
            }

            void print() const
            {
                uint64_t mem_used = memUsed();

                //Restarts stats
                printStatsLine("c restarts", numRestarts);
                printStatsLine("c time", cpu_time);
                printStatsLine("c decisions", decisions
                    , (double)decisionsRand*100.0/(double)decisions
                    , "% random"
                );

                printStatsLine("c decisions", decisions
                    , (double)decisionFlippedPolar/(double)decisions*100.0
                    , "% flipped polarity"
                );

                printStatsLine("c decisions/conflicts"
                    , (double)decisions/(double)conflStats.numConflicts
                );

                conflStats.print(cpu_time);

                /*assert(numConflicts
                    == conflsBin + conflsTri + conflsLongIrred + conflsLongRed);*/

                cout << "c LEARNT stats" << endl;
                printStatsLine("c units learnt"
                    , learntUnits
                    , (double)learntUnits/(double)conflStats.numConflicts*100.0
                    , "% of conflicts");

                printStatsLine("c bins learnt"
                    , learntBins
                    , (double)learntBins/(double)conflStats.numConflicts*100.0
                    , "% of conflicts");

                printStatsLine("c tris learnt"
                    , learntTris
                    , (double)learntTris/(double)conflStats.numConflicts*100.0
                    , "% of conflicts");

                printStatsLine("c long learnt"
                    , learntLongs
                    , (double)learntLongs/(double)conflStats.numConflicts*100.0
                    , "% of conflicts"
                );

                printStatsLine("c otf-subs"
                    , otfSubsumed
                    , (double)otfSubsumed/(double)conflStats.numConflicts*100.0
                    , "% of conflicts"
                );

                printStatsLine("c otf-subs learnt"
                    , otfSubsumedLearnt
                    , (double)otfSubsumedLearnt/(double)otfSubsumed*100.0
                    , "% otf subsumptions"
                );

                printStatsLine("c otf-subs lits gained"
                    , otfSubsumedLitsGained
                    , (double)otfSubsumedLitsGained/(double)otfSubsumed
                    , "lits/otf subsume"
                );

                cout << "c SEAMLESS HYPERBIN&TRANS-RED stats" << endl;
                printStatsLine("c advProp called"
                    , advancedPropCalled
                );
                printStatsLine("c hyper-bin add bin"
                    , hyperBinAdded
                    , (double)hyperBinAdded/(double)advancedPropCalled
                    , "bin/call"
                );
                printStatsLine("c trans-red rem bin"
                    , transRedRemoved
                    , (double)transRedRemoved/(double)advancedPropCalled
                    , "bin/call"
                );

                cout << "c CONFL LITS stats" << endl;
                printStatsLine("c confl-lits nonmin "
                    , litsLearntNonMin
                    , (double)litsLearntNonMin/(double)conflStats.numConflicts
                    , "lit/confl"
                );

                printStatsLine("c confl-lits rec-min"
                    , litsLearntRecMin
                    , (double)(litsLearntNonMin-litsLearntRecMin)/(double)litsLearntNonMin*100.0
                    , "% less"
                );

                printStatsLine("c confl-lits OTF-min"
                    , litsLearntFinal
                    , (double)(litsLearntNonMin-litsLearntFinal)/(double)litsLearntNonMin*100.0
                    , "% less"
                );

                printStatsLine("c confl-lits OTF-min call%"
                    , (double)OTFShrinkAttempted/(double)conflStats.numConflicts*100.0
                    , (double)OTFShrinkedClause/(double)OTFShrinkAttempted*100.0
                    , "% attempt successful"
                );

                printStatsLine("c confl-lits final avg"
                    , (double)litsLearntFinal/(double)conflStats.numConflicts
                );

                //General stats
                printStatsLine("c Memory used", (double)mem_used / 1048576.0, " MB");
                #if !defined(_MSC_VER) && defined(RUSAGE_THREAD)
                printStatsLine("c single-thread CPU time", cpu_time, " s");
                #else
                printStatsLine("c all-threads sum CPU time", cpu_time, " s");
                #endif
            }

            uint64_t  numRestarts;      ///<Num restarts

            //Decisions
            uint64_t  decisions;        ///<Number of decisions made
            uint64_t  decisionsAssump;
            uint64_t  decisionsRand;    ///<Numer of random decisions made
            uint64_t  decisionFlippedPolar; ///<While deciding, we flipped polarity

            uint64_t litsLearntNonMin;
            uint64_t litsLearntRecMin;
            uint64_t litsLearntFinal;
            uint64_t OTFShrinkAttempted;
            uint64_t OTFShrinkedClause;

            //Learnt stats
            uint64_t learntUnits;
            uint64_t learntBins;
            uint64_t learntTris;
            uint64_t learntLongs;
            uint64_t otfSubsumed;
            uint64_t otfSubsumedLearnt;
            uint64_t otfSubsumedLitsGained;

            //Hyper-bin & transitive reduction
            uint64_t advancedPropCalled;
            uint64_t hyperBinAdded;
            uint64_t transRedRemoved;

            //Stat structs
            ConflStats conflStats;

            //Time
            double cpu_time;
        };

    protected:
        friend class CalcDefPolars;

        //For connection with Solver
        void  resetStats();
        void  addInPartialSolvingStat();

        //For hyper-bin and transitive reduction
        size_t hyperBinResAll();
        size_t removeUselessBins();

        Hist hist;
        vector<uint32_t>    clauseSizeDistrib;
        vector<uint32_t>    clauseGlueDistrib;
        boost::multi_array<uint32_t, 2> sizeAndGlue;

        /////////////////
        //Settings
        Solver*   solver;          ///< Thread control class
        MTRand           mtrand;           ///< random number generator
        SolverConf       conf;             ///< Solver config for this thread
        bool             needToInterrupt;  ///<If set to TRUE, interrupt cleanly ASAP

        //Stats printing
        void printAgilityStats();

        /////////////////
        // Searching
        /// Search for a given number of conflicts.
        lbool search(
            const SearchFuncParams _params
            , uint64_t& rest
        );
        lbool burstSearch();
        bool  handle_conflict(SearchFuncParams& params, PropBy confl);// Handles the conflict clause
        lbool new_decision();  // Handles the case when decision must be made
        void  checkNeedRestart(SearchFuncParams& params, uint64_t& rest);     // Helper function to decide if we need to restart during search
        Lit   pickBranchLit();                             // Return the next decision variable.

        ///////////////
        // Conflicting
        void     cancelUntil      (uint32_t level);                        ///<Backtrack until a certain level.
        Clause* analyze(
            PropBy confl //The conflict that we are investigating
            , vector<Lit>& out_learnt    //learnt clause
            , uint32_t& out_btlevel      //backtrack level
            , uint32_t &nblevels         //glue of the learnt clause
            , ResolutionTypes &resolutions   //number of resolutions made
        );

        void analyzeHelper(
            Lit lit
            , int& pathC
            , vector<Lit>& out_learnt
            , bool var_bump_necessary
        );
        void     analyzeFinal     (const Lit p, vector<Lit>& out_conflict);

        //////////////
        // Conflict minimisation
        void            prune_removable(vector<Lit>& out_learnt);
        void            find_removable(const vector<Lit>& out_learnt, uint32_t abstract_level);
        int             quick_keeper(Lit p, uint32_t abstract_level, bool maykeep);
        int             dfs_removable(Lit p, uint32_t abstract_level);
        void            mark_needed_removable(Lit p);
        int             res_removable();
        uint32_t        abstractLevel(const Var x) const;
        vector<PropBy> trace_reasons; // clauses to resolve to give CC
        vector<Lit>     trace_lits_minim; // lits maybe used in minimization


        /////////////////
        //Graphical conflict generation
        void         genConfGraph     (PropBy conflPart);
        string simplAnalyseGraph (PropBy conflHalf, vector<Lit>& out_learnt, uint32_t& out_btlevel, uint32_t &glue);

        /////////////////
        // Variable activity
        vector<uint32_t> activities;
        uint32_t var_inc;
        void              insertVarOrder(const Var x);  ///< Insert a variable in heap
        void  genRandomVarActMultDiv();

        ////////////
        // Transitive on-the-fly self-subsuming resolution
        void   minimiseLearntFurther(vector<Lit>& cl);
        const Stats& getStats() const;

    private:
        //Variable activities
        struct VarFilter { ///Filter out vars that have been set or is not decision from heap
            const Searcher* cc;
            const Solver* solver;
            VarFilter(const Searcher* _cc, Solver* _solver) :
                cc(_cc)
                ,solver(_solver)
            {}
            bool operator()(uint32_t var) const;
        };

        ///Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
        void     varDecayActivity ();
        ///Increase a variable with the current 'bump' value.
        void     varBumpActivity  (Var v);
        struct VarOrderLt { ///Order variables according to their activities
            const vector<uint32_t>&  activities;
            bool operator () (const uint32_t x, const uint32_t y) const
            {
                return activities[x] > activities[y];
            }

            VarOrderLt(const vector<uint32_t>& _activities) :
                activities(_activities)
            {}
        };
        ///activity-ordered heap of decision variables
        Heap<VarOrderLt>  order_heap;

        //Clause activites
        double clauseActivityIncrease;
        void decayClauseAct();
        void bumpClauseAct(Clause* cl);


        //SQL
        friend class SQLStats;
        vector<Var> calcVarsToDump() const;
        void printRestartSQL();
        void printVarStatsSQL();
        void printClauseDistribSQL();
        PropStats lastSQLPropStats;
        Stats lastSQLGlobalStats;
        void calcVariancesLT(
            double& avgDecLevelVar
            , double& avgTrailLevelVar
        );
        void calcVariances(
            double& avgDecLevelVar
            , double& avgTrailLevelVar
        );

        //Assumptions
        vector<Lit> assumptions; ///< Current set of assumptions provided to solve by the user.

        //Picking polarity when doing decision
        bool     pickPolarity(const Var var);

        //Last time we clean()-ed the clauses, the number of zero-depth assigns was this many
        size_t   lastCleanZeroDepthAssigns;

        //Used for on-the-fly subsumption. Does A subsume B?
        //Uses 'seen' to do its work
        bool subset(const vector<Lit>& A, const Clause& B);

        double   startTime; ///<When solve() was started
        Stats    stats;
        size_t   origTrailSize;
        uint32_t var_inc_multiplier;
        uint32_t var_inc_divider;
};

inline void Searcher::varDecayActivity()
{
    var_inc *= var_inc_multiplier;
    var_inc /= var_inc_divider;
}
inline void Searcher::varBumpActivity(Var var)
{
    if ( (activities[var] += var_inc) > (0x1U) << 24 ) {
        // Rescale:
        for (vector<uint32_t>::iterator
            it = activities.begin()
            , end = activities.end()
            ; it != end
            ; it++
        ) {
            *it >>= 14;
        }

        //Reset var_inc
        var_inc >>= 14;

        //If var_inc is smaller than var_inc_start then this MUST be corrected
        //otherwise the 'varDecayActivity' may not decay anything in fact
        if (var_inc < conf.var_inc_start)
            var_inc = conf.var_inc_start;
    }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(var))
        order_heap.decrease(var);
}

inline uint32_t Searcher::abstractLevel(const Var x) const
{
    return ((uint32_t)1) << (varData[x].level % 32);
}

inline lbool Searcher::solve(const uint64_t maxConfls)
{
    vector<Lit> tmp;
    return solve(tmp, maxConfls);
}

inline uint32_t Searcher::getSavedActivity(Var var) const
{
    return activities[var];
}

inline uint32_t Searcher::getVarInc() const
{
    return var_inc;
}

inline const Searcher::Stats& Searcher::getStats() const
{
    return stats;
}

inline void Searcher::addInPartialSolvingStat()
{
    stats.cpu_time = cpuTime() - startTime;
}

inline const Searcher::Hist& Searcher::getHistory() const
{
    return hist;
}

#endif //__SEARCHER_H__
