(***     Company-Coq     ***)

(*+  Taking Proof General one step  +*)
(*+      closer to a real IDE       +*)

(*!           Clément Pit-Claudel (MIT CSAIL)          !*)
(*!         Pierre Courtieu (CNAM, Lab Cédric)         !*)

(*!               CoqPL'16, St Petersburg              !*)
(*!                    Jan 23, 2016                    !*)

(*!     https://github.com/cpitclaudel/company-coq     !*)
(*!     TODO: Link to this file     !*)


(******************************************************************************)

(*+ Intro +*)

(*! What is company-coq? !*)

(** A collection of Proof General extensions:

    * Not a new Coq IDE!
    * Rather, a new twist on a popular Coq IDE

    Company-Coq adds:

    Smart auto-completion ∙ Offline docs ∙ Snippets
    Code folding ∙ Prettified maths ∙ Lemma extraction
    Quick peek ∙ Source browsing ∙ Help with errors
    … and many other features

    Most of this is portable to other IDEs! *)

(** In this talk: a quick tour + a discussion of a few experimental directions. *)

(*! Please ask questions during the talk! !*)

(******************************************************************************)

(*+ Pretty maths! +*)

(** Without modifying the underlying text: *)

Definition PrettySymbols : (nat -> nat -> Prop) :=
  (fun (n m: nat) =>
     forall p, p <> n -> p >= m -> True \/ False).

Ltac MySimpleTactic :=
  match goal with
  | [ H: False |- _ ] => exfalso; assumption
  end.

(* begin hide *) Require Import Omega. (* end hide *)

(** Or with modifications: *)

(******************************************************************************)

(*+ Auto-completion +*)

(*!    (With documentation!)   !*)
(*!       (and snippets!)      !*)
(*!        (and sources)       !*)

(* Tactics (applin):    *) 

(* Vernacs (SLD):       *) 

(* Modules (C.N.C..D):  *) 

(* Identifiers (trunk): *) 

(* Seach results:       *)
SearchAbout plus minus.

(******************************************************************************)

(*+ Navigation +*)

(* Browsing to source: *) 

(* Looking up documentation quickly: *) 

(* Outlines *) 

(******************************************************************************)

(*+ Proof General enhancements +*)

(** Smart intros **)

Lemma SmartIntros :
  forall A (x y z: A * A),
    x = y -> y = z -> x = z.
Proof.
  
Abort.

(** Smart matches **)

Definition MatchCases (n: nat) : nat.
  
Abort.

(** Snippets! **)



(******************************************************************************)

(*+ Help with errors +*)

(** Let's look at an attempt at using Omega: *)

Lemma refl : forall x, exists (y: nat), x = y.
Proof.
  Fail omega.

  intros.
  Fail omega.
Abort.

(** Even if you know what an error means, sometimes it’s
    hard to parse. *)

(* begin hide *)
Inductive Tr {T} := TrL : T -> Tr | TrB : Tr -> Tr -> Tr.
Inductive Tt : @Tr Type -> Type := TtL : forall A, A -> Tt (TrL A) | TtBr : forall t1 t2, Tt t1 -> Tt t2 -> Tt (TrB t1 t2).

Fixpoint MkLarge {A} d (l ll:A) :=
  match d with O => TrL ll | S n => TrB (MkLarge n l l) (MkLarge n l ll) end.

Lemma inH: forall T n (t: T), inhabited (Tt (@MkLarge Type n T T)).
  intros; constructor; induction n; simpl; constructor; eauto. Qed.
(* end hide *)

Lemma LargeGoal : inhabited (Tt (@MkLarge Type 5 unit nat)).
  (* begin hide *)
  pose proof (inH unit 5 tt) as pr; simpl in *.
  Set Printing All.
  (* end hide *)
  Fail exact pr.

  

  Unset Printing All.
Abort.

(******************************************************************************)

(*+ Lemma extraction +*)

(** Company-Coq can help you structure your proofs by
    extracting lemmas: **)

Lemma my_plus_comm :
  forall p q r, (p < q /\ q < r) -> (p + q < q + r) ->
           (exists s, p + q + r < s) -> forall m n, n + m = m + n.
Proof.
  induction m; intros.
  - simpl.
    rewrite plus_0_r.
    apply eq_refl.
  - idtac.
Abort.

(** If you don't want to extract lemmas, it's ok:
    company-coq knows how to fold and unfold bullets. *)

(******************************************************************************)

(*+ Experimental features +*)

(*!        Thinking a bit bigger        !*)

(** What more can we do to make Coq more user-friendly
    (and beginner-friendly)?  

    * ‘Show Proof’ as you type
    * LaTeX rendering **)

(******************************************************************************)

(*+     Terms as you type     +*)

(*! Showin the evolution of a proof term as one !*)
(*!            steps through a proof            !*)

(* (require 'company-coq-term-builder) *)

Definition ExampleFunction : nat -> nat.
Proof.
  intros.
  refine (S _).
  refine (_ - 1).

  refine (3 * _).
  destruct H.
  + refine (1 + _).
    apply 0.
  + refine (2 + _).
    destruct H.
    * refine (3 + _).
      apply 0.
    * refine (4 + _).
      apply 1.
Defined.

Print ExampleFunction.

(******************************************************************************)

(*+ Company-Coq meets LaTeX +*)

(*!       Has anyone done this before?      !*)

(* ~/.emacs.d/lisp/company-coq/experiments/company-coq-LaTeX/example.v *)

(******************************************************************************)

(*+ Thanks! +*)

(** Next steps:

    * Get (more) feedback!
    * Discuss various proposals: documentation, TeX notations, ...
    * Share with to other IDEs! **)

(** And many thanks to Pierre Courtieu (my co-author)
    for his work on Proof General, and to Jonathan
    Leivent and Jason Gross for their tireless bug
    reports and suggestions! *)

(******************************************************************************)

(** This talk is licensed under the Creative Commons
    Attribution-ShareAlike 4.0 International License.
    To view a copy of this license, visit
    http://creativecommons.org/licenses/by-sa/4.0/. *)

(* Local Variables: *)
(* show-trailing-whitespace: nil *)
(* fill-column: 56 *)
(* End: *)
