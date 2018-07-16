Require Export Coq.Program.Tactics.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Arith.Arith_base.
Require Export Coq.Relations.Relations.
Require Export Coq.Lists.List.

Import EqNotations.
Import ListNotations.


(***
 *** Ordered Types = Types with a PreOrder
 ***)

(* NOTE: The idea with this approach is that each type uniquely determines its
ordered type, but we keep the types separate from the ordered types to make
type inference work properly... *)

Class OType (A:Type) : Type :=
  {
    oleq : relation A;
    oPreOrder :> PreOrder oleq
  }.

Instance OType_Reflexive A `{OType A} : Reflexive oleq.
Proof. typeclasses eauto. Qed.

Instance OType_Transitive A `{OType A} : Transitive oleq.
Proof. typeclasses eauto. Qed.

(* The equivalence relation for an OrderedType *)
Definition oeq {A} `{OType A} : relation A :=
  fun x y => oleq x y /\ oleq y x.

Instance oeq_Equivalence A `{OType A} : Equivalence oeq.
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H0; split; assumption. }
  { destruct H0; destruct H1; split; transitivity y; assumption. }
Qed.

Notation "x <o= y" :=
  (oleq x y) (no associativity, at level 70).
Notation "x =o= y" :=
  (oeq x y) (no associativity, at level 70).

(* FIXME: figure out what versions of this we need for rewriting! *)
Instance Proper_oleq_oleq A `{OType A}
  : Proper (oleq --> oleq ==> Basics.impl) (@oleq A _).
Proof.
  intros a1 a2 Ra b1 b2 Rb Rab.
  transitivity a1; [ assumption | ]. transitivity b1; assumption.
Qed.

Instance Subrelation_oeq_oleq A `{OType A} :
  subrelation (@oeq A _) oleq.
Proof.
  intros a1 a2 Ra; destruct Ra; assumption.
Qed.

Instance Proper_oeq_oleq A `{OType A} :
  Proper (oeq ==> oeq ==> iff) (@oleq A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry; destruct Rx; destruct Ry; split; intro Rxy.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
  transitivity x2; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance Proper_oeq A `{OType A} :
  Proper (oeq ==> oeq ==> iff) (@oeq A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry. rewrite Rx. rewrite Ry. reflexivity.
Qed.

Instance Proper_oeq_partial A `{OType A} a :
  Proper (oeq ==> Basics.flip Basics.impl) (@oeq A _ a).
Proof.
  intros x1 x2 Rx. rewrite Rx. reflexivity.
Qed.


(***
 *** Commonly-Used Ordered Types
 ***)

(* The ordered type of propositions *)
Instance OTProp : OType Prop :=
  {| oleq := Basics.impl |}.     
Proof. repeat constructor; typeclasses eauto. Defined.

(* Proofs are always related (i.e., this is the proof irrelevance type) *)
Instance OTproof (P:Prop) : OType P :=
  {| oleq := fun _ _ => True |}.
Proof.
  repeat constructor.
Defined.

(* The discrete ordered type, where things are only related to themselves; we
make this a definition, not an instance, so that it can be instantiated for
particular types. *)
Definition OTdiscrete A : OType A := {| oleq := eq |}.

(* The only ordered type over unit is the discrete one *)
Instance OTunit : OType unit := OTdiscrete unit.

(* The ordered type that flips the ordering of an underlying OType; this becomes
a type itself in Coq *)
Inductive Flip A : Type := flip (a:A).
Arguments flip {A} a.

Definition unflip {A} (f:Flip A) : A := let (x) := f in x.

Instance OTFlip A (R:OType A) : OType (Flip A) :=
  {| oleq := fun x y => unflip y <o= unflip x |}.
Proof.
  repeat constructor; intro; intros.
  - destruct x; compute; reflexivity.
  - destruct x; destruct y; destruct z; compute; transitivity a0; assumption.
Defined.

(* The discrete relation on Booleans *)
Instance OTbool : OType bool := OTdiscrete bool.

(* The pointwise relation on pairs *)
Instance OTpair A B `(OType A) `(OType B) : OType (A*B) :=
  {| oleq := fun p1 p2 => oleq (fst p1) (fst p2) /\ oleq (snd p1) (snd p2) |}.
Proof.
  repeat constructor.
  - destruct x. reflexivity.
  - destruct x. reflexivity.
  - destruct x; destruct y; destruct z; destruct H1; destruct H2;
      transitivity a0; assumption.
  - destruct x; destruct y; destruct z; destruct H1; destruct H2;
      transitivity b0; assumption.
Defined.


(* The sort-of pointwise relation on sum types *)
Inductive sumR {A B} (RA:OType A) (RB:OType B) : A+B -> A+B -> Prop :=
| sumR_inl a1 a2 : oleq a1 a2 -> sumR RA RB (inl a1) (inl a2)
| sumR_inr b1 b2 : oleq b1 b2 -> sumR RA RB (inr b1) (inr b2).

Instance OTsum A B (RA:OType A) (RB:OType B) : OType (A+B) :=
  {| oleq := sumR RA RB |}.
Proof.
  repeat constructor; intro; intros.
  { destruct x; constructor; reflexivity. }
  { destruct H; inversion H0.
    - constructor; transitivity a2; assumption.
    - constructor; transitivity b2; assumption. }
Defined.


(* The pointwise relation on functions *)
Instance OTArrow A B `{OType B} : OType (A -> B) :=
  {| oleq := fun f g => forall a, f a <o= g a |}.
Proof.
  repeat constructor.
  { intro. reflexivity. }
  { intro; intros. transitivity (y a); [ apply H0 | apply H1 ]. }
Defined.


(***
 *** Proper Instances for Simple Ordered Types
 ***)

Instance Proper_pair A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (pair : A -> B -> A*B).
Proof.
  repeat intro; split; assumption.
Qed.

Instance Proper_pair_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq ==> oeq) (pair : A -> B -> A*B).
Proof.
  intros a1 a2 Ra b1 b2 Rb; destruct Ra; destruct Rb; split; split; assumption.
Qed.

Instance Proper_fst A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (fst : A*B -> A).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_fst_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq) (fst : A*B -> A).
Proof.
  intros p1 p2 Rp. destruct Rp.
  split; eapply Proper_fst; assumption.
Qed.

Instance Proper_snd A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (snd : A*B -> B).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_snd_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq) (snd : A*B -> B).
Proof.
  intros p1 p2 Rp. destruct Rp.
  split; eapply Proper_snd; assumption.
Qed.


(***
 *** Unary Ordered Type Functors
 ***)

(* Typeclass specifying that F is an ordered type functor *)
Class OTypeF (F:forall A {RA:OType A}, Type) : Type :=
  otypeF : forall A {RA:OType A}, OType (F A).

(* Get out the OType from applying a unary functor *)
Instance OType_OTypeF F (RF:OTypeF F) A (RA:OType A) :
  OType (F A _) | 5 := RF A _.

(* Unfold uses of OType_OTypeF *)
Typeclasses Transparent OType_OTypeF.
