---------------------------- MODULE EWD840_proof ----------------------------
(***************************************************************************)
(* This module contains the proof of the safety properties of Dijkstra's   *)
(* termination detection algorithm. Checking the proof requires TLAPS to   *)
(* be installed.                                                           *)
(***************************************************************************)
EXTENDS EWD840, TLAPS

(***************************************************************************)
(* The algorithm is type-correct: TypeOK is an inductive invariant.        *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Color
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY NAssumption DEF TypeOK, Color, Nodes, vars, Next, System, Environment,
                     InitiateProbe, PassToken, SendMsg, Deactivate
<1>. QED  BY <1>1, <1>2, PTL DEF Spec


(***************************************************************************)
(* Follows a more detailed proof of the same lemma. It illustrates how     *)
(* proofs can be decomposed hierarchically. Use the "Decompose Proof"      *)
(* command (C-G C-D) to prepare the skeleton of the level-2 steps.         *)
(***************************************************************************)
LEMMA Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Color
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>. USE NAssumption DEF TypeOK, Nodes, Color
  <2>1. CASE InitiateProbe
    BY <2>1 DEF InitiateProbe
  <2>2. ASSUME NEW i \in Nodes \ {0},
               PassToken(i)
        PROVE  TypeOK'
    BY <2>2 DEF PassToken
  <2>3. ASSUME NEW i \in Nodes,
               SendMsg(i)
        PROVE  TypeOK'
    BY <2>3 DEF SendMsg
  <2>4. ASSUME NEW i \in Nodes,
               Deactivate(i)
        PROVE  TypeOK'
    BY <2>4 DEF Deactivate
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Environment, Next, System
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Prove the main soundness property of the algorithm by (1) proving that  *)
(* Inv is an inductive invariant and (2) that it implies correctness.      *)
(***************************************************************************)
THEOREM Safety == Spec => []TerminationDetection
<1>1. Init => Inv
  BY NAssumption DEF Init, Inv, Nodes
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  BY NAssumption
     DEF TypeOK, Inv, Next, vars, Nodes, Color,
         System, Environment, InitiateProbe, PassToken, SendMsg, Deactivate
<1>3. Inv => TerminationDetection
  BY NAssumption DEF Inv, TerminationDetection, terminationDetected, Nodes
<1>. QED
  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec


(***************************************************************************)
(* Step <1>3 of the above proof shows that Dijkstra's invariant implies    *)
(* TerminationDetection. If you find that one-line proof too obscure, here *)
(* is a more detailed, hierarchical proof of that same implication.        *)
(***************************************************************************)
LEMMA Inv => TerminationDetection
<1>1. SUFFICES ASSUME tpos = 0, tcolor = "white", 
                      color[0] = "white", ~ active[0],
                      Inv
               PROVE  \A i \in Nodes : ~ active[i]
  BY <1>1 DEF TerminationDetection, terminationDetected
<1>2. ~ Inv!P2  BY tcolor = "white" DEF Inv
<1>3. ~ Inv!P1  BY <1>1 DEF Inv
<1>. QED
  <2>1. Inv!P0  BY Inv, <1>2, <1>3 DEF Inv
  <2>.  TAKE i \in Nodes
  <2>3. CASE i = 0  BY <2>1, <1>1, <2>3
  <2>4. CASE i \in 1 .. N-1
    <3>1. tpos < i  BY tpos=0, <2>4, NAssumption
    <3>2. i < N  BY NAssumption, <2>4
    <3>. QED  BY <3>1, <3>2, <2>1
  <2>. QED  BY <2>3, <2>4 DEF Nodes

=============================================================================
\* Modification History
\* Last modified Tue Jun 28 18:24:01 CEST 2016 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
