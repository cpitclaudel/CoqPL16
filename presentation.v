(***    Company-Coq    ***)

(*+  Taking Proof General one step  +*)
(*+      closer to a real IDE       +*)

(*!           Clément Pit-Claudel (MIT CSAIL)          !*)
(*!         Pierre Courtieu (CNAM, Lab Cédric)         !*)

(*!               CoqPL'16, St Petersburg              !*)
(*!                    Jan 23, 2016                    !*)

(*!     https://github.com/cpitclaudel/company-coq     !*)
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

(** In this talk: a quick tour + a discussion of a few
    experimental directions. *)

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

(** Tactics (applin): *) 

(** Vernacs (SLD): *) 

(** Modules (C.N.C..D): *) 

(** Identifiers (on trunk): *) 

(** Tactic notations: *)
Tactic Notation "foo" constr(bar) "with" constr(baz) := idtac.


(** Search results: *)
Require Import List.
SearchAbout length.



(******************************************************************************)

(*+ Navigation +*)

(** Browsing to source: *)

(* rev_append *) 

(** Looking up information quickly: *)

(* length *) 

(** Browsing with outlines: *)


(******************************************************************************)

(*+ Proof General enhancements +*)

(** * Smart intros **)

Lemma SmartIntros :
  forall A (x y z: A * A),
    x = y -> y = z -> x = z.
Proof.
  
Abort.

(** * Smart matches **)

Definition MatchCases (n: nat) : nat.
  
Abort.

(** * Snippets! **)

(* mgw, Section, ... *) 


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

Lemma LargeGoal : inhabited (Tt (@MkLarge Type 3 unit nat)).
  (* begin hide *)
  pose proof (inH unit 3 tt) as pr; simpl in *.
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
  - (* Base case (m = 0) *)
    simpl.
    rewrite plus_0_r.
    apply eq_refl.
  - (* Inductive case *)
    idtac.
    
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

(*+     Terms as you type      +*)

(*! Showing the evolution of a proof term as one !*)
(*!            steps through a proof             !*)

(* (load "company-coq-term-builder.el") *)

Definition ExampleFunction (n: nat): nat.
Proof.
  intros.
  refine (S _).
  refine (_ - 1).

  refine (3 * _).
  destruct n.
  + refine (1 + _).
    apply 0.
  + refine (2 + _).
    destruct n.
    * refine (3 + _).
      apply 0.
    * refine (4 + _).
      apply 1.
Defined.

Print ExampleFunction.

(* (company-coq-TermBuilder -1) *)

(******************************************************************************)

(*+ Company-Coq meets LaTeX +*)

(*!  What happens if we use Coq notations   !*)
(*!         to produce LaTeX code?          !*)

(*! [nsum 0 n (fun x => f x)] ↦ [\sum_{x = 0}^n f(x)] !*)

(******************************************************************************)

(*+ Preliminary setup +*)

(** We start by defining a function: *)

Require Import NArith ArithRing.

Fixpoint nsum max f :=
  match max with
  | O => f 0
  | S max' => f max + nsum max' f
  end.

(** And we add a notation for it: *)

Notation "'\nsum{' x '}{' max '}{' f '}'" := (nsum max (fun x => f)).

(* begin hide *)
Infix "\wedge" := and (at level 190, right associativity).
Notation "A \Rightarrow{} B" := (forall (_ : A), B) (at level 200, right associativity).
Notation "'\ccForall{' x .. y '}{' P '}'" := (forall x, .. (forall y, P) ..) (at level 200, x binder, y binder, right associativity, format "'\ccForall{' x .. y '}{' P '}'").
Notation "'\ccNat{}'" := nat.
Notation "'\ccSucc{' n '}'" := (S n).
Infix "\times" := mult (at level 30).
(* end hide *)

(******************************************************************************)

(*+ Then the magic happens! +*)

(* (load "company-coq-latex.el") *)

Lemma Gauss:
  forall n, 2 * (nsum n (fun x => x)) = n * (n + 1).
Proof.
  intros.
  induction n.
  - (* Base case *)
    cbv [nsum].
    reflexivity.
  - (* Inductive case *)
    unfold nsum; fold nsum.
    rewrite Mult.mult_plus_distr_l.
    rewrite IHn.
    ring.
Qed.

(** Fractions work nicely as well: **)

Require Import Coq.QArith.QArith Coq.QArith.Qring Coq.QArith.Qfield.

(* begin hide *)
Notation "'\ccQ{}'" := Q.
Notation "\ccPow{ x }{ y }" := (Qpower x y).
Notation "'\ccFrac{' x '}{' y '}'" := (Qdiv x y)  : Q_scope.
Infix "\le" := Qle (at level 100).
Infix "\equiv" := Qeq (at level 100).
Infix "\times" := Qmult (at level 30).
Notation "\ccNot{ x }" := (not x) (at level 100).
Notation "x '\not\equiv' y" := (not (Qeq x y)) (at level 100).

Lemma Qmult_Qdiv_fact :
  forall a b c, not (c == 0) -> a * (b / c) == (a * b) / c.
Proof. intros; field; assumption. Qed.

Lemma Qdiv_1 :
  forall a, a / 1 == a.
Proof. intros; field. Qed.

Lemma Qplus_le_0 :
  forall a b, 0 <= a -> 0 <= b -> 0 <= a + b.
Proof.
  intros a b Ha Hb.
  pose proof (Qplus_le_compat _ _ _ _ Ha Hb) as Hab.
  ring_simplify in Hab; assumption.
Qed.

Lemma Qplus_lt_0 :
  forall a b, 0 < a -> 0 <= b -> 0 < a + b.
Proof.
  intros a b Ha Hb.
  pose proof (Qplus_lt_le_compat _ _ _ _ Ha Hb) as Hab.
  ring_simplify in Hab; assumption.
Qed.

Lemma Qmult_0 :
  forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros a b Ha Hb.
  rewrite <- (Qmult_lt_l _ _ _ Ha), Qmult_0_r in Hb; assumption.
Qed.

Lemma Qsqr_0 :
  forall a, 0 <= a ^ 2.
Proof.
  intros [n d].
  simpl; unfold Qmult, Qle; simpl.
  rewrite Z.mul_1_r; apply Z.ge_le, sqr_pos.
Qed.

Lemma Qgt_0_Qneq_0 :
  forall a, 0 < a -> not (a == 0).
Proof.
  intros [n d].
  unfold Qeq, Qlt; simpl.
  rewrite !Z.mul_1_r, Z.neg_pos_cases; intuition.
Qed.

Tactic Notation "Qside" "using" constr(lemma) :=
  try solve [repeat match goal with
                    | [ H: _ /\ _ |- _ ] => destruct H
                    end;
             auto using Qplus_le_0, Qmult_le_0_compat, Qmult_0,
             Qgt_0_Qneq_0, Qlt_le_weak, Qplus_lt_0, lemma].

Ltac Qside :=
  Qside using I.
(* end hide *)

Lemma Qfracs :
  forall a b c d,
    a > 0 /\ b > 0 /\ c > 0 /\ d > 0 ->
    (a + c)/(b + d) <= a/b + c/d.
Proof with Qside.
  intros a b c d H.
  field_simplify...
  rewrite <- Qmult_le_l with (z := b + d)...
  rewrite Qmult_div_r...
  rewrite Qmult_Qdiv_fact...
  rewrite <- Qmult_le_l with (z := b * d)...
  rewrite Qmult_div_r...
  field_simplify; rewrite !Qdiv_1...
  rewrite <- Qplus_le_l with (z := - b * d * a); ring_simplify.
  rewrite <- Qplus_le_l with (z := - b * d * c); ring_simplify.
  Qside using Qsqr_0.
Qed.

(** And you can add tactic notations to the mix! 
    (but should you?) *)

Tactic Notation "reduce" "addition" :=
  field_simplify.
Tactic Notation "multiply" "each" "side" "by" constr(term) :=
  rewrite <- Qmult_le_l with (z := term).
Tactic Notation "cancel" "numerator" "and" "denominator" :=
  rewrite !Qmult_div_r.
Tactic Notation "harmonize" "fractions" :=
  rewrite !Qmult_Qdiv_fact.
Tactic Notation "expand" "and" "collect" :=
  field_simplify; rewrite !Qdiv_1.
Tactic Notation "subtract" constr(term) "on" "each" "side" :=
  rewrite <- Qplus_le_l with (z := - term); ring_simplify.
Tactic Notation "consequence" "of" constr(lemma) := Qside using lemma.

Lemma Qfracs_take_two :
  forall a b c d,
    a > 0 /\ b > 0 /\ c > 0 /\ d > 0 ->
    (a + c)/(b + d) <= a/b + c/d.
Proof with Qside.
  intros a b c d H.
  reduce addition...
  multiply each side by (b + d)...
  cancel numerator and denominator...
  harmonize fractions...
  multiply each side by (b * d)...
  cancel numerator and denominator...
  expand and collect...
  subtract (b * d * a) on each side...
  subtract (b * d * c) on each side...
  consequence of Qsqr_0...
Qed.

(* (company-coq-LaTeX -1) *)

(******************************************************************************)

(*+ Conclusion +*)

(** Desiderata:

    * A documentation language for Gallina and Ltac
      (coqdoc is litterate programming: lacks function signatures etc.)

    * A better IDE api
      * A documented, supported XML API (Cool stuff: PIDE and PeaCoq)
      * A scripting language? Makes distributing plugins easier.
        * LuaTeX
        * FontForge
        * Blender
      * Read-only views?
      * Ltac debugger?

  *)

(** Next steps:

    * Get (more) feedback!

    * Discuss various proposals: 
      * Structured documentation format
      * Ltac debugger
      * TeX notations
      * …

    * Share with other IDEs! **)

(******************************************************************************)

(*+    Thanks! Questions?    +*)

(*!          Download company-coq at           !*)
(*! https://github.com/cpitclaudel/company-coq !*)

(*! (There's also a VM for artifact packaging, classes, etc.) !*)


(** Many thanks to Pierre Courtieu (my co-author) for
    his work on Proof General, and to Jonathan Leivent
    and Jason Gross for their tireless bug reports and
    suggestions! *)

(******************************************************************************)

(** This talk is licensed under the Creative Commons
    Attribution-ShareAlike 4.0 International License.
    To view a copy of this license, visit
    http://creativecommons.org/licenses/by-sa/4.0/. *)

(* Local Variables: *)
(* show-trailing-whitespace: nil *)
(* fill-column: 56 *)
(* End: *)
