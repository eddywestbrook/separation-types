Require Export SepTypes.OrderedType.


(***
 *** Downward Closed Sets
 ***)

Record DownSet A `{OType A} : Type :=
  { inDownSet : A -> Prop;
    downSetClosed :
      forall a1 a2, oleq a2 a1 -> inDownSet a1 -> inDownSet a2 }.

Arguments inDownSet {A _} _ _.
Arguments downSetClosed {A _} _.

Instance OType_DownSet A `{OType A} : OType (DownSet A) :=
  {| oleq ds1 ds2 := (inDownSet ds1) <o= (inDownSet ds2) |}.
Proof.
  constructor.
  - intro. reflexivity.
  - intros ds1 ds2 ds3; transitivity (inDownSet ds2); assumption.
Defined.

Instance Proper_inDownSet A `{OType A} (ds : DownSet A) :
  Proper (oleq ==> oleq --> oleq) (inDownSet (A:=A)).
Proof.
  repeat intro.
  apply H0. eapply downSetClosed; eassumption.
Qed.

Program Definition emptyDownSet {A} `{OType A} : DownSet A :=
  {| inDownSet a := False |}.

Program Definition downClose {A} `{OType A} (a:A) : DownSet A :=
  {| inDownSet a' := a' <o= a |}.
Next Obligation.
  etransitivity; eassumption.
Defined.

Instance Proper_downClose A `{OType A} :
  Proper (oleq ==> oleq) (downClose (A:=A)).
Proof.
  intros a1 a2 R12 a'; simpl; intro in_a'. etransitivity; eassumption.
Qed.

Program Definition unionDownSet {A} `{OType A} (ds1 ds2: DownSet A) : DownSet A :=
  {| inDownSet := fun a => inDownSet ds1 a \/ inDownSet ds1 a;
     downSetClosed := _ |}.
Next Obligation.
  destruct H1; [ left | right ]; eapply downSetClosed; eassumption.
Defined.

Program Definition bindDownSet {A B} `{OType A} `{OType B}
           (dsA: DownSet A) (f: A -> DownSet B) : DownSet B :=
  {| inDownSet := fun b => exists a, inDownSet dsA a /\ inDownSet (f a) b;
     downSetClosed := _ |}.
Next Obligation.
  exists H2; split; try assumption.
  apply (downSetClosed _ _ _ H1 H4).
Defined.

Instance Proper_bindDownSet A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (bindDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds f1 f2 Rf b; simpl; intro in_b.
  destruct in_b as [ a [in_ds1 in_f1]].
  exists a; split.
  - apply Rds; assumption.
  - apply Rf; assumption.
Qed.

Definition mapDownSet {A B} `{OType A} `{OType B} (f:A -> B) dsA : DownSet B :=
  bindDownSet dsA (fun a => downClose (f a)).

(* We define the fixed-point of a set function transformer f as the intersection
of all f-closed functions g *)
Program Definition fixDownSet {A B} `{OType B}
        (f: (A -> DownSet B) -> (A -> DownSet B)) (a:A) : DownSet B :=
  {| inDownSet b :=
       forall g, f g <o= g -> inDownSet (g a) b
  |}.
Next Obligation.
  apply (downSetClosed _ _ _ H0). apply H1. apply H2.
Defined.

(* NOTE: what we really want is Proper-ness of (fixDownSet f), i.e.,
w.r.t. the A argument, which only holds for functions f that are Proper
w.r.t. (oleq ==> oleq ==> oleq) *)
(*
Instance Proper_fixDownSet {A B} `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (fixDownSet (A:=A) (B:=B)).
Proof.
  admit.
Admitted.
*)

(* We then prove this is a fixed-point using the Knaster-Tarski theorem *)
Lemma fixDownSetUnfold {A B} `{OType B}
      (f: (A -> DownSet B) -> A -> DownSet B)
      (prp: Proper (oleq ==> oleq) f) :
  (fixDownSet (A:=A) (B:=B) f) =o= f (fixDownSet f).
Proof.
  assert (f (fixDownSet f) <o= fixDownSet f).
  - intros a b in_b g g_f_closed.
    assert (f (fixDownSet f) <o= g).
    + etransitivity; try eassumption. apply prp.
      intros a' b' in_b'. apply in_b'. assumption.
    + apply H0; assumption.
  - split; [ | apply H0 ].
    simpl; intros; intro; apply (H1 _ (prp _ _ H0)).
Qed.


(* We can convert a function from A to sets of B to a set of functions from A to
B, by taking the set of all functions that are in f pointwise *)
Program Definition lambdaDownSet {A B} `{OType B}
        (f: A -> DownSet B) : DownSet (A -> B) :=
  {| inDownSet := fun g => forall a, inDownSet (f a) (g a); |}.
Next Obligation.
  eapply downSetClosed; [ apply H0 | apply H1 ].
Defined.

Instance Proper_lambdaDownSet {A B} `{OType B} :
  Proper (oleq ==> oleq) (lambdaDownSet (A:=A) (B:=B)).
Proof.
  intros f1 f2 R12 g in_g a. apply R12. apply in_g.
Qed.

Definition applyDownSet {A B} `{OType B} (dsF: DownSet (A -> B)) (a:A) : DownSet B :=
  mapDownSet (fun f => f a) dsF.

(* NOTE: applyDownSet is not Proper in its A argument unless we somehow build
Proper functions from the functions in dsF... *)
Instance Proper_applyDownSet {A B} `{OType B} :
  Proper (oleq ==> eq ==> oleq) (applyDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds a1 a2 eq_a b in_b. destruct in_b as [ g [ in_g1 in_g2 ]].
  rewrite <- eq_a.
  exists g. split.
  - apply Rds; assumption.
  - assumption.
Qed.

(* NOTE: the reverse only holds when f a is non-empty for all a; i.e., when
   there is some function g such that inDownSet (f a) (g a) for all a *)
Lemma downSetBeta {A B} `{OType B} (f: A -> DownSet B) :
  applyDownSet (lambdaDownSet f) <o= f.
Proof.
  simpl; intros a b in_b.
  destruct in_b as [ g [ in_ga Rbg ]].
  eapply downSetClosed; [ apply Rbg | apply in_ga ].
Qed.
