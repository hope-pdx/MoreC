Require Import ZArith.
Require Import Defns Mem Smallstep Behaviors.
Require RTL Mach.
Require Compiler SourceMem. 
Require Import Matching Sim.

Module Thm (Import MParams: Mach.MachParameters)
          (Import CParams: Compiler.CompilerParameters).
  
  Parameter maxFrameSizeBounded2:  (CParams.maxFrameSize <= MParams.StkLimit - MParams.HpLimit)%Z.

  Module Proofs := Sim.Proofs(MParams)(CParams).
  Import Proofs.
  Import Invariants.


(* Some commands that may help with understanding the meaning of the theorem. *)
(* Locate match_vals.
Print  match_vals.
Locate match_failures.
Print  match_failures.
Locate program_behaves.
Print  program_behaves.
*)


  Section Proof.

    Variable prog: RTL.program.
    Hypothesis prog_well_typed: RTL.wt_program prog. 
    Variable tprog : Mach.program.
    Hypothesis TRANSL: match_prog prog tprog.

    Let SrcProg := RTLS.RTL_semantics (SourceMem.oracle prog) prog.
    Let TgtProg := MacS.Mach_semantics tprog.

    Theorem SemanticPreservation1 :
      forall behT,
        program_behaves TgtProg behT ->
        exists behS,
          program_behaves SrcProg behS /\ behaviour_matches match_vals match_failures behS behT.
    Proof.  
      eapply refinement_for_typed_programs; eauto.
      apply maxFrameSizeBounded2.
    Qed.

    Theorem SemanticPreservation2 :
      forall behS,
        program_behaves SrcProg behS ->
        exists behT,
          program_behaves TgtProg behT /\ behaviour_matches match_vals match_failures behS behT.
    Proof.
      eapply reverse_refinement_for_typed_programs; eauto.
      apply maxFrameSizeBounded2.
    Qed.

 End Proof.

End Thm.
