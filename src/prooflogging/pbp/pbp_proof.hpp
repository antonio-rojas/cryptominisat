#pragma once

#include <cstdint>
#include <vector>
#include <cassert>
#include <functional>
#include <string>
#include "solvertypesmini.h"

#include "prooflogging/FastStream.hpp"
#include "pbp_LitPrinter.hpp"
#include "prooflogging/ConstraintId.hpp"

using namespace CMSat;

namespace CMSat { struct Solver; }

namespace proof {
namespace pbp {
    class Proof {
        ConstraintId maxId;
        size_t formulaRead;
        FastStream stream;
        /* Solver* solver; */

    public:
        Proof(std::string filename, Solver* _solver)
            : maxId{0}
            , formulaRead(0)
            , stream(filename)
            /* , solver(_solver) */
        {
            stream << "pseudo-Boolean proof version 2.0\n";
        }

        void setExpectedClauses(int numClauses) {
            stream << "f " << numClauses << "\n";
            maxId.id = numClauses;
        }

        Proof& operator<<(const Lit& lit) {
            stream << lit.toInt();
            return *this;
        }

        void comment(std::string comment) {
            stream << "* " << comment << "\n";
        }

        Proof& operator<<(const ConstraintId& id) {
            stream << id.id;
            return *this;
        }

        template<class T>
        Proof& operator<<(const T& what) {
            stream << what;
            return *this;
        }

        ConstraintId getNextFormulaConstraintId() {
            formulaRead += 1;
            // stream << "l " << formulaRead << "\n";
            return ConstraintId(formulaRead);
        }

        ConstraintId getNewConstraintId() {
            maxId.id += 1;
            return ConstraintId{maxId.id};
        }

        uint32_t newVar() {
            assert(false && "TODO");
            /* return solver->newVar(); */
            return 1;
        }
    };

    class ContradictionStep {
        public:
            ContradictionStep(Proof& proof, ConstraintId id)
            {
                proof << "output NONE\n"
                      << "conclusion UNSAT : " << id << "\n"
                      << "end pseudo-Boolean proof\n";
                // proof << "c " << id << "\n";
            }
    };

    class DeleteStep {
        private:
            Proof& proof;
        public:
            DeleteStep(Proof& _proof) : proof(_proof) { proof << "d"; }
            void addDeletion(const ConstraintId& id) { proof << " " << id; }
            ~DeleteStep(){ proof << "\n"; }
    };

    class PBPRStep {
    private:
        Proof& proof;
        bool isDegreeSet = false;
        Lit mapTo;
        bool isMapping = false;

    public:
        const ConstraintId id;

        PBPRStep(Proof& _proof, Lit _mapTo):
            proof(_proof),
            id(_proof.getNewConstraintId()),
            mapTo(_mapTo)
        {
            isMapping = true;
            proof << "red";
        }

        PBPRStep(Proof& _proof):
            proof(_proof),
            id(_proof.getNewConstraintId())
        {
            isMapping = false;
            proof << "u";
        }

        ~PBPRStep() {
            assert(isDegreeSet);
        }

        template<typename CoeffType>
        PBPRStep& addTerm(CoeffType coeff, Lit lit) {
            proof << " " << coeff << " " << lit;
            return *this;
        }

        template<typename CoeffType>
        PBPRStep& setDegree(CoeffType degree) {
            assert(!isDegreeSet);
            proof << " >= " << degree << " ;";

            if (isMapping) {
                proof << " ";
                if (mapTo.sign()) {
                    proof << ~mapTo << " 0";
                } else {
                    proof << mapTo << " 1";
                }
            }
            proof << "\n";
            isDegreeSet = true;
            return *this;
        }
    };

    class EqualityCheck {
    private:
        Proof& proof;
        bool isDegreeSet = false;

    public:
        EqualityCheck(Proof& _proof, ConstraintId which):
            proof(_proof)
        {
            proof << "e " << which;
        }

        ~EqualityCheck() {
            assert(isDegreeSet);
        }

        template<typename CoeffType>
        EqualityCheck& addTerm(CoeffType coeff, Lit lit) {
            proof << " " << coeff << " " << lit;
            return *this;
        }

        template<typename CoeffType>
        EqualityCheck& setDegree(CoeffType degree) {
            assert(!isDegreeSet);
            proof << " >= " << degree << " " << ";" << "\n";
            isDegreeSet = true;
            return *this;
        }
    };

    class PolishNotationStep {
    private:
        Proof& proof;
    public:
        ConstraintId id;

        PolishNotationStep(Proof& _proof):
            proof(_proof),
            id(_proof.getNewConstraintId())
        {
            proof << "p";
        }

        ~PolishNotationStep(){
            proof << "\n";
        }

        PolishNotationStep& append(ConstraintId geq){
            proof << " " << geq.id;
            return *this;
        }

        PolishNotationStep& appendLit(Lit lit){
            proof << " " << lit;
            return *this;
        }

        PolishNotationStep& add(){
            proof << " " << "+";
            return *this;
        }

        PolishNotationStep& saturate(){
            proof << " " << "s";
            return *this;
        }

        PolishNotationStep& multiply(uint64_t scalar){
            proof << " " << scalar << " " << "*";
            return *this;
        }

        PolishNotationStep& floor_div(uint64_t scalar){
            proof << " " << scalar << " " << "d";
            return *this;
        }

        void split() {
            proof << " 0\n";
            proof << "p " << this->id;
            this->id = proof.getNewConstraintId();
        }
    };

    template<typename CoeffType>
    class LiteralDefinition {
    public:
        ConstraintId rightImpl;
        ConstraintId leftImpl;

        LiteralDefinition(
            Proof& proof,
            Lit def,
            std::vector<CoeffType>&& coeffs,
            std::vector<Lit>&& lits,
            CoeffType degree
        ) {
            {
                assert(lits.size() == coeffs.size());

                PBPRStep stepRightImpl(proof, ~def);
                for (size_t i = 0; i < lits.size(); i++) {
                    if (coeffs[i] < 0) {
                        lits[i] = ~lits[i];
                        coeffs[i] = -coeffs[i];
                        degree += coeffs[i];
                    }
                    assert(coeffs[i] != 0);
                    stepRightImpl.addTerm(coeffs[i], lits[i]);
                }
                stepRightImpl.addTerm(degree, ~def);
                stepRightImpl.setDegree(degree);
                rightImpl = stepRightImpl.id;
            }

            {
                PBPRStep stepLeftImpl(proof, def);
                degree = -(degree - 1);
                for (size_t i = 0; i < lits.size(); i++) {
                    degree += coeffs[i];
                    stepLeftImpl.addTerm(coeffs[i], ~lits[i]);
                }
                stepLeftImpl.addTerm(degree, def);
                stepLeftImpl.setDegree(degree);
                leftImpl = stepLeftImpl.id;
            }
        }
    };
}} //closing namespaces
