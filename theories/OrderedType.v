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


(* The pointwise relation on option types *)
Inductive optionR A `{OType A} : option A -> option A -> Prop :=
| optionR_None : optionR A None None
| optionR_Some a1 a2 : a1 <o= a2 -> optionR A (Some a1) (Some a2)
.

Instance OToption A `{OType A} : OType (option A) :=
  {| oleq := optionR A |}.
Proof.
  constructor.
  { intros [ a | ]; constructor; reflexivity. }
  { intros o1 o2 o3 R12; destruct R12; intros R23; inversion R23;
      constructor; try assumption.
    etransitivity; eassumption. }
Defined.


(* The pointwise relation on sum types *)
Inductive sumR A B `{OType A} `{OType B} : A+B -> A+B -> Prop :=
| sumR_inl a1 a2 : oleq a1 a2 -> sumR A B (inl a1) (inl a2)
| sumR_inr b1 b2 : oleq b1 b2 -> sumR A B (inr b1) (inr b2).

Instance OTsum A B `{OType A} `{OType B} : OType (A+B) :=
  {| oleq := sumR A B |}.
Proof.
  repeat constructor; intro; intros.
  { destruct x; constructor; reflexivity. }
  { destruct H1; inversion H2.
    - constructor; transitivity a2; assumption.
    - constructor; transitivity b2; assumption. }
Defined.


(* The pointwise relation on lists of equal lengths *)
Inductive listR A `{OType A} : list A -> list A -> Prop :=
| listR_nil : listR A [] []
| listR_cons a1 a2 l1 l2 : a1 <o= a2 -> listR A l1 l2 ->
                           listR A (a1 :: l1) (a2 :: l2).

Instance OTlist A `{OType A} : OType (list A) := {| oleq := listR A |}.
Proof.
  constructor.
  { intro l; induction l; constructor; try reflexivity; assumption. }
  { intros l1 l2 l3 R12; revert l3; induction R12; intros l3 R23.
    - assumption.
    - inversion R23. constructor.
      + etransitivity; eassumption.
      + apply IHR12; assumption. }
Qed.


(* The pointwise relation on functions *)
Instance OTarrow A B `{OType B} : OType (A -> B) :=
  {| oleq := pointwise_relation A oleq |}.
Proof.
  constructor; typeclasses eauto.
Defined.


(***
 *** Proper Instances for Common Operations
 ***)

(* Functions *)

(* This is needed to rewrite f to g in context (f x <o= g x) *)
Instance subrelation_OTarrow_pointwise A B `{OType B} :
  subrelation oleq (pointwise_relation A oleq).
Proof.
  intros f g Rfg. assumption.
Qed.

(* This is needed to rewrite f to g in context (f x =o= g x) *)
Instance subrelation_OTarrow_equiv_pointwise A B `{OType B} :
  subrelation oeq (pointwise_relation A oeq).
Proof.
  intros f g Rfg a. destruct Rfg. split; [ apply H0 | apply H1 ].
Qed.


(* Pairs *)

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


(* Options *)

Instance Proper_Some A `{OType A} : Proper (oleq ==> oleq) Some.
Proof.
  constructor; assumption.
Qed.

Instance Proper_Some_equiv A `{OType A} : Proper (oeq ==> oeq) Some.
Proof.
  split; constructor; destruct H0; assumption.
Qed.

(* Eliminator for the option type *)
Definition optElim {A B} (f : A -> B) (g : B) (o : option A) : B :=
  match o with
  | Some a => f a
  | None => g
  end.

(* The Proper instances for optElim are complicated by the fact that we can only
chain o if f is Proper, so we write two different Proper instances for optElim,
one that requires f to be Proper, and so it cannot change, and one that does
not, so f can change but o cannot. *)
Instance Proper_optElim1 A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> eq ==> oleq) (@optElim A B).
Proof.
  intros f1 f2 Rf g1 g2 Rg o1 o2 eq_o. rewrite eq_o. destruct o2; simpl.
  - apply Rf.
  - apply Rg.
Qed.

Instance Proper_optElim1_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq ==> eq ==> oeq) (@optElim A B).
Proof.
  intros f1 f2 Rf g1 g2 Rg o1 o2 eq_o. rewrite eq_o.
  destruct o2; simpl; try assumption.
  rewrite Rf. reflexivity.
Qed.

Instance Proper_optElim2 A B `{OType A} `{OType B} (f: A -> B) :
  Proper (oleq ==> oleq) f ->
  Proper (oleq ==> oleq ==> oleq) (optElim f).
Proof.
  intros prp g1 g2 Rg o1 o2 Ro. destruct Ro; simpl.
  - assumption.
  - apply prp; assumption.
Qed.

Instance Proper_optElim2_equiv A B `{OType A} `{OType B} (f: A -> B) :
  Proper (oleq ==> oleq) f ->
  Proper (oeq ==> oeq ==> oeq) (optElim f).
Proof.
  intros prp g1 g2 Rg o1 o2 Ro.
  destruct Rg; destruct Ro; split; apply (Proper_optElim2 A B); assumption.
Qed.


(* Sum types *)

Instance Proper_inl A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (inl : A -> A+B).
Proof.
  constructor; assumption.
Qed.

Instance Proper_inl_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq) (inl : A -> A+B).
Proof.
  split; constructor; destruct H1; assumption.
Qed.

Instance Proper_inr A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (inr : B -> A+B).
Proof.
  constructor; assumption.
Qed.

Instance Proper_inr_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq) (inr : B -> A+B).
Proof.
  split; constructor; destruct H1; assumption.
Qed.

(* Eliminator for the sum type *)
Definition sumElim {A B C} (f : A -> C) (g : B -> C) (s : A+B) : C :=
  match s with
  | inl a => f a
  | inr b => g b
  end.

(* The Proper instances for sumElim are complicated in the same way as those for
optElim, that the elimination functions f and g must be Proper in order to
change the argument being eliminated. As with optElim, we handle this with two
different instances. *)
Instance Proper_sumElim1 A B C `{OType A} `{OType B} `{OType C} :
  Proper (oleq ==> oleq ==> eq ==> oleq) (@sumElim A B C).
Proof.
  intros f1 f2 Rf g1 g2 Rg s1 s2 eq_s. rewrite eq_s. destruct s2; simpl.
  - apply Rf.
  - apply Rg.
Qed.

Instance Proper_sumElim1_equiv A B C `{OType A} `{OType B} `{OType C} :
  Proper (oeq ==> oeq ==> eq ==> oeq) (@sumElim A B C).
Proof.
  intros f1 f2 Rf g1 g2 Rg s1 s2 eq_s; destruct Rf; destruct Rg; split;
    apply (Proper_sumElim1 A B C); try assumption.
  symmetry; assumption.
Qed.

Instance Proper_sumElim2 A B C `{OType A} `{OType B} `{OType C}
         (f: A -> C) (g: B -> C) :
  Proper (oleq ==> oleq) f ->
  Proper (oleq ==> oleq) g ->
  Proper (oleq ==> oleq) (sumElim f g).
Proof.
  intros prp_f prp_g s1 s2 Rs.
  destruct Rs; simpl; rewrite H2; reflexivity.
Qed.

Instance Proper_sumElim2_equiv A B C `{OType A} `{OType B} `{OType C}
         (f: A -> C) (g: B -> C) :
  Proper (oleq ==> oleq) f ->
  Proper (oleq ==> oleq) g ->
  Proper (oeq ==> oeq) (sumElim f g).
Proof.
  intros prp_f prp_g s1 s2 Rs.
  destruct Rs; split; apply (Proper_sumElim2 A B C); assumption.
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
