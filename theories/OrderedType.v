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

Arguments oleq {_ _} : simpl never.

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


(***
 *** Some General Proper Instances
 ***)

(** Any operations that are Proper for oleq are Proper for oeq **)

Instance Proper_oeq_oleq_op1 A B `{OType A} `{OType B} (f: A -> B) :
  Proper (oleq ==> oleq) f -> Proper (oeq ==> oeq) f.
Proof.
  intros prp a1 a2 Ra; destruct Ra; split; apply prp; assumption.
Qed.

Instance Proper_oeq_oleq_op2 A B C `{OType A} `{OType B} `{OType C}
         (f: A -> B -> C) :
  Proper (oleq ==> oleq ==> oleq) f -> Proper (oeq ==> oeq ==> oeq) f.
Proof.
  intros prp a1 a2 Ra b1 b2 Rb; destruct Ra; destruct Rb.
  split; apply prp; assumption.
Qed.

Instance Proper_oeq_oleq_op3 A B C D `{OType A} `{OType B} `{OType C} `{OType D}
         (f: A -> B -> C -> D) :
  Proper (oleq ==> oleq ==> oleq ==> oleq) f ->
  Proper (oeq ==> oeq ==> oeq ==> oeq) f.
Proof.
  intros prp a1 a2 Ra b1 b2 Rb c1 c2 Rc; destruct Ra; destruct Rb; destruct Rc.
  split; apply prp; assumption.
Qed.

Instance Proper_oeq_oleq_op4 A B C D E
         `{OType A} `{OType B} `{OType C} `{OType D} `{OType E}
         (f: A -> B -> C -> D -> E) :
  Proper (oleq ==> oleq ==> oleq ==> oleq ==> oleq) f ->
  Proper (oeq ==> oeq ==> oeq ==> oeq ==> oeq) f.
Proof.
  intros prp a1 a2 Ra b1 b2 Rb c1 c2 Rc d1 d2 Rd.
  destruct Ra; destruct Rb; destruct Rc; destruct Rd.
  split; apply prp; assumption.
Qed.

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

(* The complete order on unit is the same as the discrete one, but easier to
prove things about... *)
Instance OTunit : OType unit := {| oleq := fun _ _ => True |}.
Proof.
  repeat constructor.
Defined.
(* Instance OTunit : OType unit := OTdiscrete unit. *)

(* The discrete ordered type, where things are only related to themselves; we
make this a definition, not an instance, so that it can be instantiated for
particular types. *)
Definition OTdiscrete A : OType A := {| oleq := eq |}.

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

(* The ordered type that requires equivalence in the underlying OType *)
Inductive Equiv A : Type := equiv (a:A).
Arguments equiv {A} a.

Definition unequiv {A} (f:Equiv A) : A := let (x) := f in x.

Instance OTEquiv A (R:OType A) : OType (Equiv A) :=
  {| oleq := fun x y => unequiv y =o= unequiv x |}.
Proof.
  constructor; intro; intros.
  - reflexivity.
  - etransitivity; eassumption.
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

(* Lift order relation to subset types by ignoring the proof term. *)
Instance OTsubset A `{OType A} {P : A -> Prop} : OType {a : A | P a} :=
  {| oleq := fun x y => proj1_sig x <o= proj1_sig y |}.
Proof.
  constructor.
  - firstorder.
  - unfold Transitive. etransitivity; eauto.
Defined.


(* The sort-of pointwise relation on sum types *)
Inductive sumR {A B} (RA:OType A) (RB:OType B) : A+B -> A+B -> Prop :=
| sumR_inl a1 a2 : a1 <o= a2 -> sumR RA RB (inl a1) (inl a2)
| sumR_inr b1 b2 : b1 <o= b2 -> sumR RA RB (inr b1) (inr b2).

Instance OTsum A B (RA:OType A) (RB:OType B) : OType (A+B) :=
  {| oleq := sumR RA RB |}.
Proof.
  repeat constructor; intro; intros.
  { destruct x; constructor; reflexivity. }
  { destruct H; inversion H0.
    - constructor; transitivity a2; assumption.
    - constructor; transitivity b2; assumption. }
Defined.


(* NOTE: the following definition requires everything above to be polymorphic *)
(* NOTE: The definition we choose for OTType is actually deep: instead of
requiring ot_Type A = ot_Type B, we could just require a coercion function from
ot_Type A to ot_Type B, which would yield something more like HoTT... though
maybe it wouldn't work unless we assumed the HoTT axiom? As it is, we might need
UIP to hold if we want to use the definition given here... *)
(*
Program Definition OTType : OType :=
  {|
    ot_Type := OType;
    oleq := (fun A B =>
               exists (e:ot_Type A = ot_Type B),
                 forall (x y:A),
                   oleq A x y ->
                   oleq B (rew [fun A => A] e in x)
                        (rew [fun A => A] e in y));
  |}.
*)


(***
 *** The Ordered Type for Functions
 ***)

(* The type of continuous, i.e. Proper, functions between ordered types *)
Record OFun A B {RA:OType A} {RB:OType B} :=
  {
    ofun_app : A -> B;
    ofun_Proper : Proper (oleq ==> oleq) ofun_app
  }.

(* New idea: never unfold applications of proper functions directly during
simplification, because the Proper proofs can get big from substitution;
instead, we will only use rewriting to simplify proper functions *)
Arguments ofun_app {_ _ _ _} !o _.
Arguments ofun_Proper [_ _ _ _] _ _ _ _.

Notation "A '-o>' B" :=
  (OFun A B) (right associativity, at level 99).

Notation "x @@ y" :=
  (ofun_app x y) (left associativity, at level 20).

(* The non-dependent function ordered type *)
Instance OTarrow A B `{OType A} `{OType B} : OType (A -o> B) :=
  {| oleq :=
       fun f g =>
         forall a1 a2, a1 <o= a2 -> ofun_app f a1 <o= ofun_app g a2 |}.
Proof.
  repeat constructor; intro; intros.
  { apply ofun_Proper; assumption. }
  { transitivity (ofun_app y a1).
    - apply H1; reflexivity.
    - apply H2; assumption. }
Defined.

(* OType instance for non-proper functions. 
   TODO: rename *)
Instance OTarrow' A B `{OType A} `{OType B} : OType (A -> B) :=
  {| oleq := fun f g => forall x, f x <o= g x |}.
Proof.
  repeat constructor; intro; intros.
  { reflexivity. }
  { etransitivity; eauto. }
Defined.


(***
 *** Proper Instances for Simple Ordered Types
 ***)

Instance Proper_pair A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (pair : A -> B -> A*B).
Proof.
  repeat intro; split; assumption.
Qed.

Instance Proper_fst A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (fst : A*B -> A).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

Instance Proper_snd A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (snd : A*B -> B).
Proof.
  intros p1 p2 Rp; destruct Rp; assumption.
Qed.

(* ofun_app is always Proper *)
Instance Proper_ofun_app A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (@ofun_app A B _ _).
Proof.
  intros f1 f2 Rf a1 a2 Ra. apply Rf; assumption.
Qed.

(*
Instance Proper_ofun_app_partial A B `{OType A} `{OType B} f :
  Proper (oleq ==> oleq) (ofun_app (A:=A) (B:=B) f).
Proof.
  apply ofun_Proper.
Qed.
*)


(***
 *** Unary Ordered Type Functors
 ***)

(* Typeclass version of OTypeF1Fun *)
Class OTypeF (F:forall A {RA:OType A}, Type) : Type :=
  otypeF : forall A {RA:OType A}, OType (F A).

(* Get out the OType from applying a unary functor *)
Instance OType_OTypeF F (RF:OTypeF F) A (RA:OType A) :
  OType (F A _) | 5 := RF A _.

Typeclasses Transparent OType_OTypeF.
